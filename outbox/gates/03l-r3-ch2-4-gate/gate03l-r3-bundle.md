## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03l-pack-r3.md =====

# Gate 03l ([PS10] ch. 2–4, the `Randomized/Build/` machine layer and the clean-module host), round 3: delta audit pack

**What is audited:** the repair of round 2, on `cryptography/pass-shelat-ch2-4` at `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95` (the merge of
[Shilun-Allan-Li/tcslib#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206), the gate 03 repair batch, and the records commits of 2026-11-06).
- **The round 2 findings** are `findings/gate03l-r2-findings.md` (in the bundle, verbatim), and the resolutions `resolutions-03l-r2.md`.
- **The repair:** #206's diff (`evidence-repairs/03-batch/repair.diff.txt`; it covers five gates, and only this pack's files are under audit) and the records changes named in the resolutions.
- **The deliverable:** **`gate03l-r3-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header. **The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

1. **Verify each resolution** of `resolutions-03l-r2.md`: fixed, recorded, scheduled, or not resolved (and why).
2. **Audit the changed surface afresh:**
   - **the head envelopes of H14** (the major): `Clean.envelope`, `host_call_envelope`, `host_clean_envelope`. Restate each; does the set meet policy §1's head-envelope requirement for a public host contract, as the round 2 finding asked? Are their bounds correct (coarse bounds from the time bound)?
   - the eight `simps` equations and the new lemmas in `axioms-03l.log` (minor 2).
3. **Check that nothing else changed** in this pack's files: the statement diff (`statements.txt`) lists every added and changed declaration of the batch.

Pack 03a's severity guide applies. Attempt at least one adversarial instantiation against the changed surface. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Findings, resolutions, the diff | as above |
| Under audit, at the pin | `TuringMachine/Build/ModuleHost.lean`; records: `machine-library-design.md` §14 (row H14), `duplication-ledger.md` (DL-20), `resolutions-03l-r1.md` |
| Context | `03l-pack.md` and earlier round packs, `03a-pack.md`, `policy.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03-batch/`)

- **Elaboration** (`replay.log`): the 128 modules downstream of #206's 21 changed files, then `audits/pass-shelat/Checks`, each checked alone after a base sync (`base-sync.log`): **129 of 129 pass, 0 errors**; every module's `sorry` count equals the base. A maintainer re-check of 8 key modules also passes (`maintainer-recheck.log`).
- **Axioms** (`axioms.log`, `axioms-03l.log`): 549 prints over the 21 files, compared with the base: no axiom set changed; the 10 new lemmas are standard.
- **Seal** (`seal.log`): the consumers of `ProverBounded` pass sealed (their base versions fail); the new proofs pass with the definitions they could unfold sealed.
- **Lint** (`lint.log`): `scripts/style_lint.py` and `scripts/campaign_style_lint.py --check8b`, compared with the base: no new finding.
- **Statements** (`statements.txt`): 10 added, 2 changed (the two ruled ones in `NP.lean`), 0 removed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per resolution row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`. The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03l-r2-findings.md =====

# Gate 03l, round 2 — external findings

**Verdict: DO NOT CLOSE — 0 blockers, 1 major, 3 minors.** The round-1 empty-axiom-log major is repaired. No false executable definition or theorem statement was identified. The remaining major concerns the newly gated H14 host contract's missing head-envelope interface, required by the supplied repository policy; it does not invalidate the two existing polynomial-time consumers.

Audited pin: `e28773ef3bda6f7b4b112ec1657427bfef01e374`; the pack identifies its Lean files with #203 head `f29be161cd86cfc3a9c38bd203bfa095b4974086`. Bundle: 26 sections, SHA-256 `11239bba11abce836d5d863c309583a4be5cf28ff063eae01898b22999a51f94`.

Scope: the changed trusted surface in section A, every new public declaration named by the brief (including the generated equations), the round-1 resolutions, H14's contract, and SAT's instantiation in section B. Tactic proofs were not audited. No fresh Lean replay or kernel axiom print was performed; the execution logs remain maintainer attestations. Independent checks comprised source/diff comparison, declaration censuses, mathematical adversarial instantiations and finite parser simulations.

Supplemental reads, all pinned: [round-1 repair axiom log](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03l/axioms.log), [#203 axiom log](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03l-cleanup1/axioms.log), and SAT at [#203's base](https://github.com/Shilun-Allan-Li/tcslib/blob/0c348ff94cacf24d96d99078c9dd9e328530c8d2/TCSlib/Complexity/ClassNP/SAT.lean) and [the closing pin](https://github.com/Shilun-Allan-Li/tcslib/blob/e28773ef3bda6f7b4b112ec1657427bfef01e374/TCSlib/Complexity/ClassNP/SAT.lean). The two axiom logs are referenced by the resolution but not included as sections of this bundle; their absence was not treated as proof that the evidence did not exist.

Lean filenames below are under `TCSlib/Complexity/`; the six randomized machine files are under `Randomized/Build/`, and `ModuleHost.lean` is under `TuringMachine/Build/`. Line numbers refer to extracted source files. Source pages use book page = PDF page − 12. Numbered findings 1–4 require action; the remaining rows give the requested declaration coverage and adversarial checks.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `TuringMachine/Build/ModuleHost.lean:197,462,530` · `Clean`, `host_call`, `host_clean`; `machine-library-design.md:3090` · H14 | H14 has the required time and control-state clauses, but its newly public contract lacks the required intermediate head-envelope clause. | `policy.md:113–115` expressly requires time and space/head-envelope clauses for a public host; §14 of the design repeats this requirement. The exported statements specify the terminal tapes and head positions, but no intermediate head positions, space bound, or transport of a module envelope. A two-tape module can preserve the argument on tape 0, move tape 1 through positions `0,1,2,3,2,1,0,0`, and first halt at step 7 without writing or emitting. It satisfies `Clean M id (fun _ => []) (fun _ => 7)` for every native input and argument, including the empty argument. Thus a clean terminal seam is not an intermediate envelope. This is a contract-completeness finding, not a counterexample to an existing theorem; the time bound does imply a coarse envelope. | Publish a documented inclusive head-envelope corollary for a call, or an envelope-transport lemma plus its bounded-call corollary. A coarse bound derived from unit head moves and `t ≤ B arg.length` suffices for the present time-only consumers; do not infer a smaller bound from the terminal word. Alternatively, obtain an explicit scoped exception for H14 and record its payback before closing the contract gate. |
| 2 | minor | `03l-pack-r2.md` · attestation 2; `evidence/l2/axioms.log` | The 139-entry log covers every explicitly written public theorem/lemma, not every public theorem including generated equations. | An independent name census matches all 139 explicit theorem/lemma declarations exactly. Eight public `simps` equations are absent: `IterateFind.copyTM_k`, `ModuleHost.hostTM_k`, `ModuleHost.hostTM_tm_q₀`, and `PairParse.cfg_state`, `cfg_inputPos`, `cfg_workTapes`, `cfg_workTapePos`, `cfg_output`. These are simple generated equations, so this is narrower than round 1's empty-log major. | Add those eight axiom prints, or qualify the attestation as covering explicitly written theorems and separately account for the generated equations. Do not describe 139 as the exhaustive public-theorem census. |
| 3 | minor | `resolutions-03l-r1.md:47` · M5; `03l-pack-r2.md` · attestation 4; `evidence/l2/lint.log` | The check-8/8b repair is evidenced, but the claim that round 2's attestation records that stronger lint is inaccurate. | `evidence-repairs/03l-cleanup1/lint-after.log` includes the stronger check and has no check-8/8b warnings for the seven in-scope files. Nevertheless both the new pack and `evidence/l2/lint.log` still identify `scripts/style_lint.py`, the presence-only checker. The separate stronger evidence prevents this from becoming an evidence major. | Point the closing attestation to the stronger log and name its actual command; distinguish its scoped clean result from unrelated warnings/failures elsewhere in that log. |
| 4 | minor | `resolutions-03l-r1.md:57` · final scheduling paragraph; `duplication-ledger.md:47` · DL-20 | The two records give different schedules for the first-halt duplication. | The resolutions place DL-20 under work found for clean-up part 2. DL-20 instead says to move `first_halt`/`live_prefix` upstream at the main landing and labels the item merely noted. Neither wording establishes that these two milestones are the same. The disclosed duplicate itself is not a new undisclosed-copy finding. | Choose the intended milestone and make the resolution and ledger agree, including the accepted status and owner/PR or named work item. Keep this separate from DL-17, whose part-2 deferral is consistently recorded. |
| 5 | note | Evidence · round 1 finding 1 | The empty axiom attestation is substantively repaired. | The referenced historical log was fetched at the round-2 pin: 107 output entries, 106 distinct names, including the 90 old public theorems and 16 consumers; `polyTimeComputable_blockMap` is duplicated. All dependencies are standard. The separately fetched #203 log has 268 prints, including the seven repetition headlines and `SAT_reducible_SAT3`, with no `sorryAx`. The supplied current log covers all 139 explicit in-scope theorems. These are checked maintainer execution records, not a new auditor kernel run. | No change required. |
| 6 | note | Evidence · repair diff, statement preservation, replay and seals | The supplied delta is consistent with the delivered sources and the claimed public-statement preservation. | Every section-A hunk matched the delivered new file exactly when reversed. The two primitive transition-table definitions and all retained pure loop definitions are unchanged; the three in-scope existence/repetition headlines retain their statements. After the namespace substitution, all 17 retained `BlockMapLoop` declarations retain their statements. SAT's two public definitions retain their bodies, and all five public declarations retain their signatures. The supplied replay lists 27 successful modules and 17 imported admission warnings; the eight in-scope seal consumers pass with the stated controls and explicit limitations. | No change required. |
| 7 | note | Source comparison · [PS10] §2.1, book pp. 21–24 / PDF pp. 33–36; Algorithm 38.5 and following repetition, book pp. 38–39 / PDF pp. 50–51 | No new source-fidelity discrepancy was found in the changed machine infrastructure. | The source requires total deterministic computation and worst-case time over randomized tapes, and uses bounded repetition returning the first successful result. The host/parser are implementation infrastructure, not textbook lemmas attributed verbatim to PS10. Their explicit budgets and the existing `R+1` tested-state convention are retained. Coin independence remains a consumer/probability obligation, not a theorem of this deterministic host. | No change required. |
| 8 | note | `ModuleHost.lean:197` · `Clean` | The definition agrees with its repaired docstring. | A module has at least one work tape. For every native input and argument, starting live at its canonical seam with empty output, it first halts at some positive time bounded solely by the argument length; the final seam has `result arg` on tape 0, all other work tapes blank, all heads restored, and output exactly `emit arg`. The actual running time may depend on the native input; the result, emission and bound may not. | No change required. |
| 9 | note | `ModuleHost.lean:207` · `clean_iff` | The characterization agrees with its docstring. | It expands `Clean` into exactly the positive tape-count condition, universal input/argument quantification, positive bounded first-halt time, live strict prefix, and full terminal-configuration equality. It neither drops a conjunct nor adds a hypothesis. | No change required. |
| 10 | note | `ModuleHost.lean:385,389` · `State`, `state_eq` | Both the generalized type abbreviation and its equation agree with their prose. | `State C M` is the disjoint sum of a host-control state in `C` and a tagged internal state of one of the finitely indexed modules. `state_eq` identifies that type with `C ⊕ Σ i, (M i).State`. Different modules' internal states cannot collide. | No change required. |
| 11 | note | `ModuleHost.lean:394,398` · `entry`, `entry_eq` | Both declarations agree with their docstrings. | `entry M i` is the module tag `i` paired with that module's start state, in the right summand. The equation states this for arbitrary module count and control type; it is not tied to either consumer. | No change required. |
| 12 | note | `ModuleHost.lean:409` · `hostTM` | The machine definition agrees with its docstring and is generic in every variation named by the brief. | It takes the finite module family, common tape count, finite control type, control transition table, return map, and start state. A control state executes the supplied table; a module state executes its padded transition, retaining emissions and mapping live successors back into that module, with a halt mapped to `ret i`. Tape padding introduces no extra transitions. H14's omitted envelope is finding 1. | No change required. |
| 13 | note | `ModuleHost.lean:408` · generated `hostTM_k`, `hostTM_tm_q₀` | The generated projections match the defining machine. | `hostTM_k` states that the host has exactly the supplied `K` tapes. `hostTM_tm_q₀` states that its initial control is exactly the supplied `q₀`. Their parent definition supplies the prose; neither is registered as a simp lemma by this attribute. | No change required. |
| 14 | note | `ModuleHost.lean:424` · `hostTM_step_inl` | The statement agrees with the control-step docstring. | From any configuration whose state is `some (.inl c)`, one host transition is precisely the action selected by `ctrl c` on the currently scanned symbols. It requires no clean seam and imposes no unjustified restriction on the consumer's control action. | No change required. |
| 15 | note | `ModuleHost.lean:269` · `clean_install` | The statement agrees with its docstring. | Every polynomial-time word function has some finite clean module with a polynomial argument-length budget that installs its value and emits nothing. The existential machine and polynomial are chosen once, before the universal native-input and argument quantifiers inside `Clean`. | No change required. |
| 16 | note | `ModuleHost.lean:293` · `clean_emit` | The statement agrees with its docstring. | Every polynomial-time word function has some finite clean module that restores its argument and emits precisely the function value, with a polynomial argument-length budget. It does not install the emitted value as the resident word. | No change required. |
| 17 | note | `ModuleHost.lean:462` · `host_call` | The generalized exact-time call statement agrees with its docstring. | Given a module run live at every time before `t` and halted cleanly at `t`, the host started at that module's entry with prefix `pre` reaches its return seam at the same `t`, with result word and output `pre ++ out`; no host-control state occurs at any time strictly below `t`. The terminal configuration forces `t>0` even though it is not a separate hypothesis. The arbitrary terminal-state parameter `q` is erased by `state := none`. | No change required. |
| 18 | note | `ModuleHost.lean:530` · `host_clean` | The statement agrees with the repaired bounded-call docstring. | For every native input, argument and prefix, a `Clean` module yields a host call of some duration `0<t≤B(arg.length)`, with the same result/emission maps, return seam, and exclusion of every control state before the endpoint. No extra dispatch charge is inserted inside that call; any surrounding control steps are paid by the consumer. | No change required. |
| 19 | note | `ModuleHost.lean:509` · `guard_add` | The statement agrees with its docstring. | Two consecutive run segments avoiding one specified state on their strict prefixes yield a segment avoiding it before the sum of their durations. The intermediate configuration is exactly the first segment's endpoint. If the second duration is positive, its guard includes its time zero, preventing an unnoticed anchor visit at the join. | No change required. |
| 20 | note | `ModuleHost.lean:92` · `first_halt` | The statement agrees with its docstring. | A live configuration that is halted by time `t` has a first halt at a positive `u≤t`; all earlier configurations are live, and the whole configuration at `u` equals that at `t`. This is for an arbitrary raw deterministic machine, not just a clean module. Its duplication schedule is finding 4. | No change required. |
| 21 | note | `ModuleHost.lean:111` · `live_prefix` | The statement agrees with its docstring. | If a run is live at time `t`, it is live at every time `u≤t`, including both endpoints. This uses the absorbing meaning of halt and has no assumption of eventual termination. | No change required. |
| 22 | note | `ModuleHost.lean:311` · `request_budget` | The statement agrees with its docstring. | For natural parameters with `d≤D` and `m+1≤N`, it bounds `A*(m+1)^d` by `A*N^D`. The second hypothesis already forces `N>0`, avoiding the zero-base monotonicity trap; `A=0` and `d=D=0` are harmless. | No change required. |
| 23 | note | `IterateFindHost.lean:259,270` · `hostCtrl`, `hostCtrl_eq` | The new control definition and its total equation agree with their docstrings. | Control 0 silently dispatches to module 2. Control 1 silently dispatches to module 4 exactly when tape 0 reads `some true`, and to module 3 otherwise, including a blank. Control 2 silently halts. All these actions are stationary, and the native input symbol is ignored. The equation covers every `Fin 3` state. | No change required. |
| 24 | note | `IterateFindHost.lean:283` · `hostRet` | The changed result type preserves the return map and matches the docstring. | The five returns are respectively module 1's entry, control 0, control 1, control 0, and control 2. The new type is the generalized host state with `C = Fin 3`; it does not alter the underlying destinations. | No change required. |
| 25 | note | `IterateFindHost.lean` · `hostRet_zero` | The case equation agrees with its docstring. | It states that module 0 returns to module 1's entry. Together the five equations exhaust `Fin 5`. | No change required. |
| 26 | note | `IterateFindHost.lean` · `hostRet_one` | The case equation agrees with its docstring. | It states that module 1 returns to control `.inl 0`. Together the five equations exhaust `Fin 5`. | No change required. |
| 27 | note | `IterateFindHost.lean` · `hostRet_two` | The case equation agrees with its docstring. | It states that module 2 returns to control `.inl 1`. Together the five equations exhaust `Fin 5`. | No change required. |
| 28 | note | `IterateFindHost.lean` · `hostRet_three` | The case equation agrees with its docstring. | It states that module 3 returns to control `.inl 0`. Together the five equations exhaust `Fin 5`. | No change required. |
| 29 | note | `IterateFindHost.lean` · `hostRet_four` | The case equation agrees with its docstring. | It states that module 4 returns to control `.inl 2`. Together the five equations exhaust `Fin 5`. | No change required. |
| 30 | note | `IterateFindHost.lean:312,317` · `hostTM`, `hostTM_eq` | The abbreviation and its reading equation preserve the repetition host. | The host is `ModuleHost.hostTM` with five modules, `K+1` tapes, `hostCtrl`, `hostRet`, and module 0's entry as start. The equation names this whole instantiation; changing `def` to `abbrev` permits the generic host statements to apply without changing the transition behavior. | No change required. |
| 31 | note | `IterateFindHost.lean:66` · generated `copyTM_k`; `copyTM`, `copy_clean` | The generated tape-count equation agrees with the unchanged copier. | `copyTM_k` states that there is one work tape. Its two-state table and exact positive `2*x.length+2` copying/rewinding contract are retained. This native-input copier is intentionally used through `host_call`, not claimed to satisfy input-independent `Clean`. | No change required. |
| 32 | note | `IterateFindHost.lean:324` · `host_dispatch` | The renamed-type statement agrees with its unchanged meaning and docstring. | From the anchor seam, one stationary silent step enters the verdict module with the same resident word. The old `hostEntry` is replaced by the generalized `ModuleHost.entry`. | No change required. |
| 33 | note | `IterateFindHost.lean:336` · `host_branch` | The renamed-type statement agrees with its docstring. | If the resident word's first bit is `b`, one stationary silent step selects module 4 for true and module 3 for false, preserving the seam word. Its explicit first-bit hypothesis is appropriate; the more general blank case is specified by `hostCtrl_eq`. | No change required. |
| 34 | note | `IterateFindHost.lean:352` · `host_halt` | The renamed-type statement agrees with its docstring. | From control 2 at the seam, with any output already present, one step halts and leaves all tapes, heads and output unchanged. | No change required. |
| 35 | note | `PairSplit.lean:94` · `PairParse.cfg` | The new shared configuration definition agrees with its docstring. | It constructs a one-work-tape configuration with optional state `q`, native input `x`, input position `i+1` for `i≤x.length`, resident buffer `a`, arbitrary integer work-head position `z`, and output `out`. The extra one accounts for the left input end marker. | No change required. |
| 36 | note | `PairSplit.lean:93` · generated `cfg_state`, `cfg_inputPos`, `cfg_workTapes`, `cfg_workTapePos`, `cfg_output` | All five generated field equations match the parent definition. | Respectively they return `q`; the finite input position with value `i+1`; the buffer tape of `a` on the unique work tape; head position `z`; and output `out`. The bound proof does not affect the stored configuration. These are the five parser equations omitted from the axiom census in finding 2. | No change required. |
| 37 | note | `PairSplit.lean:100` · `cfg_inputSymbol` | The statement agrees with its docstring. | The scanned input symbol is `x[i]?`; it is the right blank when `i=x.length`. This configuration family does not include the left input end marker. | No change required. |
| 38 | note | `PairSplit.lean:121` · `cfg_workTapeSymbols` | The statement agrees with its docstring. | The unique scanned work symbol is the buffer tape evaluated at integer position `z`. Negative positions and positions beyond the stored word are included. | No change required. |
| 39 | note | `PairSplit.lean:112` · `cfg_congr` | The statement agrees with its docstring. | When the input indices are equal and all other supplied data are the same, the two configurations are equal, regardless of their bound proofs. It does not assert equality of configurations with different buffers or outputs. | No change required. |
| 40 | note | `PairSplit.lean:130` · `apply_cfg_stay` | The statement agrees with its docstring. | A non-writing action that leaves the input head fixed, moves the work head by `d`, emits optional bit `o`, and chooses state `q'` produces index `i`, unchanged buffer, head `z+d`, and output `out ++ o.toList`. It is an action equality, so it is correctly stated even for `q=none`. | No change required. |
| 41 | note | `PairSplit.lean:141` · `apply_cfg_advance` | The statement agrees with its docstring. | The analogous non-writing action advances the input index to `i+1`, changes the work head to `z+d`, and appends the optional emission. The hypothesis `i+1≤x.length` ensures the initial position is not the right blank; no unclamped boundary step is falsely asserted. | No change required. |
| 42 | note | `PairSplit.lean:153` · `parse_first` | The statement matches the parser docstring, for its stated empty-output configurations. | Under the first-half transition-table agreement, one step after prefix `pre` of `pre ++ b :: rest` consumes `b` and enters the state remembering it, without changing the buffer or its right-blank head position. The theorem specializes the unchanged output to `[]`. | No change required. |
| 43 | note | `PairSplit.lean:181` · `parse_block` | The statement agrees with its three-case docstring. | Under both table agreements, two steps consume the aligned block. Equal bits append one stored bit and advance the work head; `10` halts without changing the buffer; `01` enters rewind with the work head at the integer position `a.length-1`. The input index advances by two and output remains empty in all cases. The two concrete consumers satisfy these agreements, so the interface is nonvacuous. | No change required. |
| 44 | note | `PairSplit.lean:219` · `rewind_run` | The statement agrees with its docstring. | For every `j≤a.length`, starting at work position `(j:ℤ)-1`, exactly `j+1` rewind steps reach position zero in state `n`, preserving the native input position, buffer and arbitrary output prefix. At `j=0` the start is `-1`, not natural-number subtraction clamped to zero. | No change required. |
| 45 | note | `IterateFind.lean:105` · `step_eq` | The equation agrees with its docstring and repairs the cross-file reading API. | It tests the length of the new value `g (pairSndD w)` against `P.eval x.length`; if it fits, the result is the encoded pair of `x` and that value, otherwise the original raw word. The equation is total, not restricted to a reachable or well-formed state. | No change required. |
| 46 | note | `StateLoop.lean:200` · `gstep_eq` | The equation agrees with its docstring. | It applies the supplied step to the entire raw word, tests the resulting length against the bound at the decoded first-component length, and either encodes that first component together with the result or leaves the original word unchanged. This is distinct from `IterateFind.step`, which applies `g` to a decoded second component. | No change required. |
| 47 | note | `StateLoop.lean:211` · `gstepBound_eval` | The evaluation equation agrees with its docstring. | For every natural `n`, the bound expression evaluates to `3*n+2+B.eval n`. The equation is about evaluation of the polynomial syntax, not a new run theorem. | No change required. |
| 48 | note | `StateLoop.lean:297` · `IterLoop.start_eq` | The equation agrees with its docstring. | The initial state pairs an empty unary counter with the input word. | No change required. |
| 49 | note | `StateLoop.lean:306` · `IterLoop.step_eq` | The equation agrees with its docstring. | For a state word retaining the input outside the counter/orbit pair, it prepends true to the decoded counter and applies `g` to the decoded orbit point. The outer retained input is reattached by `orbit`, not returned by this step. | No change required. |
| 50 | note | `StateLoop.lean:315` · `IterLoop.acc_eq` | The equation agrees with its docstring. | Acceptance means that the decoded counter length is at least `R` evaluated at the retained input length. The comparison is inclusive, not equality. | No change required. |
| 51 | note | `StateLoop.lean:323` · `IterLoop.out_eq` | The equation agrees with its docstring. | The output is the second component of the second component, namely the decoded orbit point. | No change required. |
| 52 | note | `StateLoop.lean:364` · `EmitLoop.start_eq` | The equation agrees with its docstring. | It pairs an empty counter with the pair consisting of the input orbit point and an empty accumulator. | No change required. |
| 53 | note | `StateLoop.lean:375` · `EmitLoop.step_eq` | The equation agrees with its docstring. | For the decoded counter, orbit point and accumulator, it increments the counter, advances the point by `g`, and appends the emission of the old point to the accumulator. The literal projection formula also covers malformed raw words. | No change required. |
| 54 | note | `StateLoop.lean:387` · `EmitLoop.out_eq` | The equation agrees with its docstring. | It returns the decoded accumulator followed by the emission of the current orbit point. Thus the final point's emission is included once. | No change required. |
| 55 | note | `StringLoops.lean:71` · `MajLoop.start_eq` | The equation agrees with its docstring. | The remaining word is the whole input, and the true/false counters both start empty. | No change required. |
| 56 | note | `StringLoops.lean:84` · `MajLoop.step_eq` | The equation agrees with its docstring. | It removes one remaining bit and increments its corresponding unary counter, reading an empty remaining word as false. That default is correctly exposed even though normal loop execution stops before stepping an empty remainder. | No change required. |
| 57 | note | `StringLoops.lean:98` · `MajLoop.acc_eq` | The equation agrees with its docstring. | Acceptance is exactly emptiness of the decoded remaining word. | No change required. |
| 58 | note | `StringLoops.lean:107` · `MajLoop.out_eq` | The equation agrees with its docstring. | It returns the single Boolean asserting that the true-counter length is at least the false-counter length plus one. Empty input and ties therefore produce false. | No change required. |
| 59 | note | `StringLoops.lean:208` · `XorLoop.start_eq` | The equation agrees with its docstring. | It initializes the two remaining components from the total pair projections of `z`, with an empty accumulator. | No change required. |
| 60 | note | `StringLoops.lean:221` · `XorLoop.step_eq` | The equation agrees with its docstring. | It removes one bit from each remaining component and appends their head-bit xor to the accumulator, using false defaults for empty components. | No change required. |
| 61 | note | `StringLoops.lean:236` · `XorLoop.acc_eq` | The equation agrees with its docstring. | Acceptance is emptiness of either remaining component, so the loop stops at the shorter component. | No change required. |
| 62 | note | `StringLoops.lean:245` · `XorLoop.out_eq` | The equation agrees with its docstring. | It returns exactly the decoded accumulator. | No change required. |
| 63 | note | `StringLoops.lean:252` · `XorLoop.rounds_eq` | The equation agrees with its docstring. | The number of rounds is the minimum of the two decoded component lengths, including zero. | No change required. |
| 64 | note | `StringLoops.lean:374` · `EqLoop.step_eq` | The equation agrees with its docstring. | It removes the two heads and replaces the mismatch flag by `[true]` if their xor is true; otherwise it preserves the flag. Head defaults are false. | No change required. |
| 65 | note | `StringLoops.lean:390` · `EqLoop.out_eq` | The equation agrees with its docstring. | It returns true precisely when both remaining components and the mismatch flag are empty. It therefore checks equality of the full components, not just their common-length prefixes. | No change required. |
| 66 | note | `StringLoops.lean:400` · `EqLoop.flag_eq` | The equation agrees with its docstring. | The flag after index `i` is empty when the two `take i` prefixes are equal and `[true]` otherwise; it is defined for every natural index. | No change required. |
| 67 | note | `StringLoops.lean:524` · `BlockMapLoop.start_eq` | The equation agrees with its docstring. | It initializes the remainder to the second component of `z` and the accumulator to empty. | No change required. |
| 68 | note | `StringLoops.lean:537` · `BlockMapLoop.step_eq` | The equation agrees with its docstring and hides the now-private helper correctly. | It drops a block of length `b.eval (pairFstD (pairFstD v)).length` from the decoded remainder and appends `g` of that block to the accumulator. The equation states the block length explicitly rather than exposing private `blk`. | No change required. |
| 69 | note | `StringLoops.lean:550` · `BlockMapLoop.acc_eq` | The equation agrees with its docstring. | It accepts when remainder length plus one is at most the block length, or the block length is zero. Over naturals these are exactly a strictly short remainder or a zero block length. | No change required. |
| 70 | note | `StringLoops.lean:560` · `BlockMapLoop.out_eq` | The equation agrees with its docstring. | It returns the decoded accumulator. | No change required. |
| 71 | note | `StringLoops.lean:569` · `BlockMapLoop.rounds_eq` | The equation agrees with its docstring. | The round count is natural division of the second-component length by the block length determined from the first-component length, with result zero when that divisor is zero. | No change required. |
| 72 | note | Changed projection/test docstrings · `EmitLoop.point_poly`, `accum_poly`; `MajLoop.rest_poly`, `trues_poly`, `falses_poly`; `XorLoop.fstRest_poly`, `sndRest_poly`, `accum_poly`, `xorBit_poly`; `BlockMapLoop.param_poly`, `rest_poly`, `accum_poly` | All twelve now state the polynomial-time property actually asserted. | The EmitLoop pair extracts orbit point and accumulator; the majority triple extracts remainder and the two counters; the xor quartet extracts both remainders and accumulator and computes a singleton default-head xor; the block-map triple extracts parameter, remainder and accumulator. `param_poly` now correctly allows any first-component contents, using only their length. None of these theorem statements changed. | No change required. |
| 73 | note | Changed orbit docstrings · `IterLoop.orbit_eq`, `EmitLoop.orbit_eq`, `MajLoop.orbit_eq`, `XorLoop.orbit_eq`, `EqLoop.orbit_eq`, `BlockMapLoop.orbit_eq` | All six revised descriptions match their existing quantified ranges and values. | IterLoop gives counter `1^i` and `g^[i] x` for every `i`; EmitLoop also gives the concatenation of emissions at indices below `i`. Majority counts true/false bits of the consumed prefix for `i≤w.length`. Xor and equality give the two dropped suffixes and respectively the consumed xor prefix or mismatch flag for `i` no larger than the shorter component. BlockMap gives the dropped suffix and concatenated block values for every `i`, without claiming those arbitrary later blocks are all full. | No change required. |
| 74 | note | `StringLoops.lean` · all 17 `BlockLoop` → `BlockMapLoop` renames | The namespace repair preserves every retained definition and theorem statement. | The five definitions `start`, `step`, `acc`, `out`, `rounds` retain their bodies. `param_poly`, `rest_poly`, `accum_poly`, `start_poly`, `step_poly`, `acc_poly`, `out_poly` retain the corresponding polynomial-time assertions. `orbit_eq` retains its exact state formula; `orbit_length_le` retains its polynomial bound through the full-block round count; `acc_orbit_false`/`acc_orbit_true` retain the strict-before/exact-end tests; `out_orbit` retains the concatenation over full blocks. `blk` alone becomes private, and no public statement needs its private name. | No change required. |
| 75 | note | Changed sketches and private parser adapters · `IterateFind.lean`, `IterateFindHost.lean`, `PairSplit.lean`, `UnaryMul.lean`, `Repetition.lean`; DESIGN §2.4/§2.6 | The substantive construction descriptions are synchronized and no headline is weakened. | The machine invariant is an actual encoded pair, the guard tests the proposed new point, and the release flag, padding, two-state copier, five-module host, common budget, exact fuel and inclusive counter test are described. `stepWord_verdictWord` now states its identity without an unnecessary admissibility qualifier. Both primitive machines supply explicit first-half, second-half and rewind table agreements to the same public parser; their tables and headline bounds are unchanged. DESIGN's phrase about no redirected transitions should be read as referring to the original live exit targets: the generic host still forwards a module halt to its return state. | No change required. |
| 76 | note | H14 · SAT consumer, section B | SAT instantiates all the generic parameters without changing its public meanings. | It uses `C=Unit`, six modules and the same returns: `0→1`, `1→anchor`, `2→3`, `3→4`, `4→5`, `5→anchor`; the anchor silently dispatches to module 2, and startup begins in module 0. The native-input appender uses `host_call`, while input-independent install/emit modules use `host_clean`. The stronger all-control-state guard specializes to the old unique-anchor guard. Both `SAT`/`SAT3` definitions and the three public theorem signatures were independently compared at #203's base and the closing pin. | No change required. |
| 77 | note | Adversarial instantiation · zero tapes, zero budget, immediate halt | The contract is neither vacuous everywhere nor permissive about degenerate clean calls. | A zero-tape machine fails `0<M.k`. If `B(0)=0`, substituting the empty argument forces `0<t≤0`, a contradiction. Conversely a one-tape stationary machine that halts on its first action preserves every argument and satisfies `Clean M id (fun _ => []) (fun _ => 1)`. For `host_call`, trying `t=0` contradicts its halted endpoint because the initial state is `some`. | No change required. |
| 78 | note | Adversarial instantiation · arbitrary prefix, return state, controller and start state | The time and no-control-visit clauses have the needed local scope. | Let a one-tape module halt in one stationary step while emitting true. With prefix `[false]`, the host endpoint at time 1 has output `[false,true]`, the unchanged argument, and exactly the chosen `ret i`; at time zero it is in a module summand. Choosing a hostile controller, an unrelated `q₀`, or returning directly to a module cannot invalidate this `runFrom` statement. Returning to the same entry may create an infinite overall host run; no theorem here claims global termination. | No change required. |
| 79 | note | Adversarial instantiation · parser separator, rejection and empty rewind | The shared parser handles the boundary cases that are easy to break during extraction. | From empty buffer on input `[false,true]`, two steps enter rewind at input index 2 and work position `-1`; one further rewind step reaches position zero. On `[true,false]`, two steps halt with empty output and unchanged buffer. On `00`/`11`, the buffer grows by one bit. For `rewind_run` at `j=0`, even an empty buffer and a nonempty pre-existing output are preserved after the single step from `-1` to zero. | No change required. |
| 80 | note | Adversarial instantiation · rejected growth and zero-size blocks | The repaired reading lemmas expose the correct boundary semantics. | With `x=[]`, `P=var`, `g s=true::s`, and `w=pairEncode [] []`, the new point has length 1 while the bound is 0, so `IterateFind.step_eq` yields `w`; the former design's old-length guard would grow it. With block length zero and `g([])=[true]`, `rounds_eq` gives zero and `acc_eq` gives true immediately, so the executed loop returns an empty accumulator rather than emitting a phantom block. For block length 2 and a three-bit remainder, exactly one full block is mapped. | No change required. |
| 81 | note | Adversarial instantiation · restored heads versus visited heads | The new host's terminal seam does not supply the missing public envelope. | For the two-tape module in finding 1, states 0–2 move tape 1 right, states 3–5 move it left, and state 6 halts without moving; tape 0 and native input never move and nothing is written or emitted. Its first halt is at 7, its terminal seam is exact for every argument, yet tape 1 visits cell 3 on empty argument. This is a concrete witness to the distinction underlying the policy finding, not a purported violation of the existing time theorem. | No change required. |
| 82 | note | Adversarial instantiation · release flag with equal entry and exit | The harvested stopping construction does not introduce a zero-time return. | For a callable one-state stationary self-loop with entry equal to exit, the first positive exit is step 1. The wrapper starts with its release flag false, performs that step and raises the flag, then halts at step 2. The install/emit budget includes the wrapper step; `first_halt` cannot select time zero because the initial state is live. | No change required. |
| 83 | note | Independent finite semantic checks | The generic parser's tested boundary and interior instances agree with the statements. | A separate Python transition interpreter checked 6,076 first-half/aligned-block instances (all prefixes and suffixes of length at most 2, buffers of length at most 4, and all four bit pairs) and 15,351 rewind instances (all native inputs/output prefixes of length at most 2, buffers of length at most 4, every admissible input index and rewind index). These finite checks found no discrepancy; they are not Lean executions or universal proofs. | No change required. |

## Round 1 resolution checks

- 1: fixed — the formerly empty evidence now exists, covers the requested historical constructions and consumers, and is corroborated by the current explicit-theorem log; finding 2 is the narrower generated-equation census issue.
- 2: fixed — the as-built erratum corrects the new-value guard, actual-pair invariant, release wrapper, padding, copier, budget and counter test; the frozen text is explicitly identified as historical.
- 3: fixed — the 38 requested reading equations are present (including generated projections), `blk` is private, and the re-pointed consumers have the supplied seal evidence; the additional host/parser equations were checked above.
- 4: fixed — all thirteen cited theorem docstrings, `Clean`'s omitted conjuncts, and the optional orbit descriptions are repaired without changing the asserted mathematics.
- 5–20, 22: recorded — unchanged accepted observations; the changed primitive tables and headline statements were compared, the source comparison was rechecked, and new adversarial checks are given above. Historical finite tests remain historical, not claimed as rerun.
- 21: fixed — the old-guard counterexample is now recorded in the erratum and the actual new-value guard still rejects it.
- 23–37, 39–53, 56–71, 73, 75–80, 82–83, 86–91, 93–97, 103: recorded — unchanged private-statement readings stand; note 65's wording is fixed, and the copied host/parser bodies were removed or replaced by shared interfaces. The separate H14 contract finding remains open.
- 38, 54, 72, 74, 84, 85, 98, 104, 105, 107–111, 114, 120–122, 127–130, 135–139, 145–148, 156–164, 174–182, 186–196, 206–214: recorded — retained public statements are unchanged modulo the declared moves and namespace rename; the changed host statements are restated above.
- 55, 81, 99–101, 125, 126, 131–134, 140–142, 149–152, 165–169, 183–185, 197–202: fixed — the appropriate total equations or predicate characterization are supplied; `step_eq` is used for the bridge and the block-map equations use the renamed namespace.
- 106, 143, 144, 153–155, 170–173, 203–205: fixed — the repaired prose now states the bounded-call or polynomial-time assertion, including the arbitrary first-component parameter convention.
- 92, 102: fixed — the copier's tape-count projection and the generic host's tape-count/start-state projections provide the requested reading API. Their omission from the axiom census is finding 2, not an absent lemma.
- 112, 113, 115–119: scheduled — the seven FP-toolkit/length facts remain present, as disclosed by DL-17; clean-up part 2 after #195 is the named deferral, not a claim of completed deduplication.
- 123, 124: recorded — both orbit recursion equations retain `@[simp]` under the recorded R-03l-2 ruling; no new unapproved simp attributes were found in the repair.
- M1(a): not resolved as an overall host-contract closure — the duplicate layers are removed, both consumers use the public host, and H14 is registered, but the newly gated public host lacks the policy-required envelope in finding 1.
- M1(b): fixed — UnaryMul consumes `Turing.PairParse`; its copied configuration/parse lemmas are deleted and rewind is an instance of the shared theorem.
- M1(c): scheduled — DL-17 remains the explicitly deferred part-2 toolkit cleanup.
- M1(d): recorded — H14 and IterateFindHost's provenance disclose the parallel input copier; no claim that it was deduplicated is made.
- M2: fixed — Repetition's construction and theorem sketch describe the built route, including the stronger machine invariant and the bridge through `IterateFind.step_eq`.
- M3: fixed — all 17 retained block-map declarations are renamed consistently, with unchanged statements, and Repetition’s references are updated consistently.
- M4: fixed — both functions retain their declared roles, and the cross-file equality now reads `IterateFind.step_eq` before reducing Repetition's own definition.
- M5: not resolved in the attestation wording — the stronger lint actually ran and its in-scope result is clean, but the claimed updated attestation still names the presence-only checker; finding 3 is the remaining minor.
- M6: recorded — the two simp attributes have the stated R-03l-2 approval.
- Additional part-2 record, five old orbit reads: scheduled — the seal log identifies exactly five old zero-case reads in four files and shows the same failures in old and new versions; they are not regressions of this repair.
- Additional part-2 record, DL-20: not resolved as a consistent schedule — the duplicate is disclosed, but part 2 and main landing are different recorded milestones; finding 4 asks only for reconciliation.

## H14 contract disposition

The host is generic in everything the two consumers vary. Its call duration is exactly the source module's duration, bounded positively in `host_clean`; its strict-prefix exclusion of every control state is stronger than either consumer's single-anchor requirement. It supports arbitrary output prefixes and returns directly to another module as well as to a control state. These clauses suffice for a third consumer with the same canonical-seam, polynomial-time use. They do not claim global termination, arbitrary scratch-tape frames, or an intermediate head envelope. The last omission prevents closing H14 under the supplied policy until finding 1 is resolved or explicitly excepted. SAT's public statements and definitions are preserved.

## Notation

`⟨a,b⟩` means `pairEncode a b`; `[]` is the empty bit word; `++` is list concatenation; `1^i` is the list of `i` true bits; `g^[i]` is the `i`-fold iterate of `g`. All other symbols are the parameters or declaration names of the cited Lean statements.


## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03l-r2.md =====

# Gate 03l (the `Randomized/Build/` machine layer and the clean-module host): round 2 resolutions

- **Round:** findings `findings/gate03l-r2-findings.md`, SHA-256 `f62ddbf98aad38786f122cd7a51c1ad30e858bb0913eaffcde87fb923fe1574b`; pin `e28773ef`. **0 blockers, 1 major, 3 minors**; round 1's major repaired.
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| 1 | major | **Fixed** (#206, item B). `Turing.ModuleHost.Clean.envelope` (every work head within `B |arg|` of the origin at every time of a clean module's run), `host_call_envelope` (within `t` cells for all `v ≤ t`, from the call seam), `host_clean_envelope` (`host_clean`'s conclusion plus the envelope `B |arg|`). These are coarse bounds from the time bound, through `MultiTapeTM.workTapePos_step_le` and `workTapePos_runFrom_mem_Icc`; the docstrings say the contract gives nothing sharper. Registry row H14 lists them. No existing statement changes. |
| 2 | minor | **Fixed.** `evidence-repairs/03-batch/axioms-03l.log` prints the eight `simps`-generated equations and the three new lemmas; all standard. |
| 3 | minor | **Fixed.** The round 3 attestation names `campaign_style_lint.py --check8b` and its log. |
| 4 | minor | **Fixed (records).** DL-20's milestone is the `main` landing in both the ledger and `resolutions-03l-r1.md`. |
| 5–10 | note | No change. |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/repair.diff.txt =====

diff --git a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
index 66f802b8..c51a6ff4 100644
--- a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
@@ -38,6 +38,11 @@ inside one finite machine.
   the host: from the host seam at the module's entry state, with any output prefix, the host
   reaches the seam at the module's return state with the module's result word, forwarding exactly
   the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
+* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
+  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
+  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
+  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
+  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).
 
 ## Origin
 
@@ -62,6 +67,8 @@ machines, the control states and their table, the return map and the start state
   clean install and a clean emit module with a polynomial budget on the argument length.
 * `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
   that no control state is visited; `guard_add` — chaining guarded segments.
+* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
+  envelopes of a clean module and of a host call.
 * `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
   liveness of the prefix of a live run.
 * `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
@@ -213,6 +220,44 @@ theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B :
           state := none, output := emit arg} :=
   Iff.rfl
 
+/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
+then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
+seam at its start state holding `arg` (before, at and after its first halt), every work head is
+within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
+and the run is constant from `t` on. The contract gives nothing sharper: it fixes the terminal
+seam, not the intermediate head positions, and a clean module may move a head out and back
+before it halts at the seam (gate 03l round 2, finding 1).
+
+**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
+within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
+is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
+`MultiTapeTM.runFrom_of_halt`). -/
+theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
+    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
+    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
+      (B arg.length : ℤ) := by
+  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
+  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
+      none := by
+    rw [hend]
+  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
+      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
+        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
+    rcases le_total v t with hvt | htv
+    · exact ⟨v, hvt, rfl⟩
+    · refine ⟨t, le_rfl, ?_⟩
+      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
+  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
+    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
+  rw [Cfg.ofWords_workTapePos] at h1 h2
+  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
+  rw [hu, abs_le]
+  constructor <;> omega
+
 /-- Turn a clean-call bridge contract into the uniform first-halting form.
 
 **Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
@@ -503,6 +548,42 @@ theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
   · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
     exact host_seam M K ret i hp x result pre out q none
 
+/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
+endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
+`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
+where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
+the duration of the call, so this bounds the heads throughout the call.
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
+`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
+tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
+physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
+origin, so the host's heads obey any head envelope of the module.
+
+**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
+at the origin, and `v ≤ t`. -/
+theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
+    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
+        j| ≤ (t : ℤ) := by
+  intro v hv j
+  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
+      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
+    intro c hc
+    obtain ⟨h1, h2⟩ :=
+      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
+    rw [hc] at h1 h2
+    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
+    rw [abs_le]
+    constructor <;> omega
+  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)
+
 /-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
 and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
 from `c` avoids `anchor` before time `a + b`. -/
@@ -545,4 +626,38 @@ theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
     host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
   exact ⟨t, hp, ht, hguard, hend⟩
 
+/-- **A clean module call inside the host, with its head envelope** (the bounded call of
+`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
+emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
+prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
+output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
+`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
+every time `v ≤ t` has every work head within `B |arg|` cells of the origin.
+
+The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
+the sharper envelope inherited from the module).
+
+**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
+`t ≤ B |arg|`, gives the envelope. -/
+theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M)
+    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
+    (h : Clean (M i) f g B) (x arg pre : List Bool) :
+    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
+      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
+          ≠ some (.inl c)) ∧
+      (hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
+        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
+      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+          v).workTapePos j| ≤ (B arg.length : ℤ) := by
+  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
+  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
+  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
+  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB
+
 end Turing.ModuleHost
diff --git a/TCSlib/Cryptography/Asymptotic/OneWay.lean b/TCSlib/Cryptography/Asymptotic/OneWay.lean
index b2445e44..7ac5de06 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWay.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWay.lean
@@ -281,8 +281,9 @@ theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 
   simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]
 
 /-- **The literal form implies the `1^n` form when the output length determines the
-parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
-audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
+parameter** (injective `outLen`, equivalently non-constant output length for these polynomial
+lengths; repair of the run-3 audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a
+`1^n`-inverter `B` is the literal
 inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
 and `B.advice n` at the output length and leaves its extra coins unread.
 
diff --git a/TCSlib/Cryptography/Candidates/Concrete.lean b/TCSlib/Cryptography/Candidates/Concrete.lean
index 59dac7c5..938af1fa 100644
--- a/TCSlib/Cryptography/Candidates/Concrete.lean
+++ b/TCSlib/Cryptography/Candidates/Concrete.lean
@@ -519,6 +519,15 @@ def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List B
     if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- Block rejection sampling unfolded: `rejectBlocksL E k B T r` is the first `some v` over
+`t ∈ [0, T)` (`List.findSome?` over `List.range T`) with `v` the number read from the first `k`
+bits of the `t`-th block of `B` bits of `r`, kept iff `E v`. -/
+theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
+    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
+      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
+      else none :=
+  rfl
+
 /-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
 bits, `listToNat_lt_two_pow`). -/
 theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 767d14fe..b7fbd309 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -49,7 +49,8 @@ collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀
 as an argument.
 
 **Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
-the `1/q` term of Theorem 107.3) the prime must have full length `2^{n−1} ≤ p`. This is
+the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
+hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
 demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
 `Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
 loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
@@ -316,9 +317,11 @@ def FullLength : Prop :=
 
 /-- The generator outputs primes of full length `n` **except on a set of coins of probability
 at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
-rejection sampler, D10). Needed, with `Negligible δ`, where the proofs divide by `q` or
+rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
 `p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
-are discarded and contribute at most `δ n`. Whether safe primes (resp. primes `≡ 3 (mod 4)`
+are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
+a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
+review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
 with a generator) of full length can be produced for every `n` except with negligible
 probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
 unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
@@ -467,6 +470,15 @@ def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
     if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
+`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
+review, M2). -/
+theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
+    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
+  funext r
+  rw [rejectBlocksL_eq]
+  rfl
+
 /-- A sampled value is below `m`. -/
 theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
     v < m := by
@@ -484,18 +496,15 @@ distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
 `expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
 `ddhExpo`).
 
-**Proof sketch.** `k ≤ n` by `Nat.size_le`, so trial `t < n` reads the first `k` bits of the
-`t`-th block of `n` bits of `List.ofFn b` (`NumberTheory.chunk`; `List.drop`/`List.take` of
-`List.ofFn`), and `sampleBelowL m k n n` is `firstHit (· < m)` of the numbers read from the
-blocks (`List.findSome?` over `List.range n` versus `List.finRange n`; `listToNat` of the `k`
-bits is `bitsToNat` of the block's prefix, `bitsToNat_eq_listToNat`). The map from the `n · n`
-coins to the `n` prefixes is a product of coordinate projections, so it pushes the uniform
-distribution to the uniform one on `Fin n → Fin k → Bool` (`StatClose.comp_pushesUniform`),
-and reading bits is the bijection `bitsEquiv k` onto `Fin (2^k)`; `statClose_firstHit` with
-`E = {x < m}` and `d = 0` gives closeness `(1 − m/2^k)^n ≤ (1/2)^n` (`Nat.lt_size_self`:
-`m/2^k ≥ 1/2`), transported along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` by
-`StatClose.comp_equiv_right` and `StatClose.map` (`Fin.val`), exactly as in
-`statClose_rejectionSample`. -/
+**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
+filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
+`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
+(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
+`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
+the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
+`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
+target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
+(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
 theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
     StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
       (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
@@ -514,7 +523,7 @@ def expSampleRaw (z : List Bool) : List Bool :=
 domain `D_i`"] given the arithmetic bundle.
 
 **Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
-leading zeros stripped (requested shared primitive, as in the RSA sampler); the trial loop is
+leading zeros stripped (`H.size`); the trial loop is
 `Complexity.polyTimeComputable_iterateFind` over the `n` blocks of `1^n` bits
 (`polyTimeComputable_pairDropPoly`), each trial comparing the first `k` bits with `m`
 (`H.le`); the payload is the accepted block, the `none` branch gives the fallback; the output
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
index 14900a0d..8c1cc2b3 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
@@ -558,24 +558,36 @@ set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f
 `expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
 `orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
 `Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
-success is `predProb (expo g_u) (halfBit (p−1)) A_i` with `A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`.
-Apply `invProb_dlInverter_ge` with `s := ⌊ε(p−1)/4⌋ ≥ 1` (as `p − 1 ≥ 2^{n−1} − 1 ≥ 8n^c` for
-large `n`), `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n · (2n^c)² = 16 n^{2c+1}`: the inverter
-succeeds on the good instances with probability `≥ (3/4)/T ≥ 3/(4(8n^c + 1))`, hence overall
-`≥ (ε/2) · 3/(4(8n^c + 1))` (`OneWay.uprob_mul_le_uexp`-style averaging over the good set). The
-machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, 1^{n}⟩`, coins
-`T·n + n·ℓ·(2n + A.coins)` (all `PolyExpr`), on `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`,
-computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`), samples `t` and the `r_{j,i}` by
-rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by
-`statClose_rejectionSample`/`StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), shifts
-`y · g^{−ts}` (`H.modExp`, `H.xgcd` for the inverse), and runs the `n` rounds of `dlLoop`
-(`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11): quadratic
-residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by `H.modExp`
-(`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
-`⟨⟨⟨1^n, ⟨i, z_i⟩⟩, A.advice n⟩, ρ_i⟩` (`polyTimeComputable_iterateEmit`, `NUPPT.polyTimeComputable_layout`),
-the comparison with `half(r_i)` (`halfStr`), the majority (`polyTimeComputable_majority`), the
-negation `p − z` and the bit assembly; finally `(bits + ts) mod (p−1)` as an `n`-bit numeral
-(`decodeFin n` reads it back, `bitsToNat_natToBits`). Thus `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`
+success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
+`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
+Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
+`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
+(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
+`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
+succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
+The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
+(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
+`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
+and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
+`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
+`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the
+good instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
+`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
+`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the
+`n` rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`,
+D11): quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
+`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
+`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
+`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the
+majority (`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
+`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
+`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
+of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of
+`A` are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
+`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
+`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
+`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n`
+`= 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
 for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
 theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
     (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
diff --git a/TCSlib/Cryptography/Candidates/ElGamal.lean b/TCSlib/Cryptography/Candidates/ElGamal.lean
index 1f1d1ab4..be4efe98 100644
--- a/TCSlib/Cryptography/Candidates/ElGamal.lean
+++ b/TCSlib/Cryptography/Candidates/ElGamal.lean
@@ -56,10 +56,11 @@ generator's coins (`ExpGroupGen.FullLengthExcept`).
 
 **Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
 `Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
-`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — the two ensembles
-then had different instance laws whenever `q` varies with the coins, and the threshold test
-`[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every
-randomized generator. The seeds are now product types (uniform coins for the generator, D6)
+`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — so the two ensembles
+could have different instance laws, and when `q` varies non-negligibly with the coins (two
+orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a
+threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons
+unrelated to DDH. The seeds are now product types (uniform coins for the generator, D6)
 with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
 (full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.
 
@@ -294,8 +295,8 @@ run-3 audit P2-2, by instance resolution).
 
 Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
 the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
-depended on the fibre sizes and differed from `ddhRandom`'s (cubes), making `DDHAssumption`
-false for every generator whose `q` varies with the coins. -/
+depended on the fibre sizes and differed from `ddhRandom`'s (cubes), which could make
+`DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20). -/
 noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
   σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
   X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
@@ -509,9 +510,9 @@ def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
 (`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
 layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
 rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
-test `H.le` (the decrement `p − 1` and the bit length `Nat.size` are requested shared
-primitives, as in the RSA generator); `h = g² mod p` and `h^x mod p` by `H.modExp`; the
-numerals are padded to width `n` (`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
+test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
+`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
+(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
 theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
     PolyTimeComputable (egGenRaw G) := by
   sorry
@@ -843,8 +844,11 @@ except on a negligible set of the generator's coins (and under the arithmetic hy
 **Deviation:** message space `G_q` and the chosen-message form of security (the text's
 `m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
 and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
-makes the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of probability
-`δ n`; the text leaves the proof as an exercise and omits the generator-versus-square term.
+is used to make the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of
+probability `δ n` (a convenience: if `E[1/q]` were not negligible, a DDH distinguisher finding
+`a` by exhaustive search when `q ≤ 2n^c` would contradict the DDH assumption, so `hbig` could be
+dropped; gate 03f1 review, M1; ruling R-03f1-1 (A) keeps it); the text leaves the proof as
+an exercise and omits the generator-versus-square term.
 
 Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
 is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
diff --git a/TCSlib/Cryptography/Candidates/Factoring.lean b/TCSlib/Cryptography/Candidates/Factoring.lean
index 42944c08..0566c08f 100644
--- a/TCSlib/Cryptography/Candidates/Factoring.lean
+++ b/TCSlib/Cryptography/Candidates/Factoring.lean
@@ -499,11 +499,17 @@ with the step dropping `n` bits, the test `hP` on the first `n` bits, the payloa
 bits, `R = 2n²`, `P = var`), whose `List.range.find?` form is `firstHit` over `chunk`
 (`samplePrime`); the fallback numeral `natToList n 2 = 0^{n-2}10` of a failed run is the
 `none` branch of `iterateFind` (a constant string of unary-polynomial length,
-`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`); the acceptance test of
-`samplePairOut` is two `H.prime` calls, a `pairEq` test and two `H.le`
-comparisons with `1^{max n 2}` (`polyTimeComputable_ite`), the accepted blocks are re-encoded
-with `max n 2` bits (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the
-default pair is a constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). The acceptance test of
+`samplePairOut` uses `hP` only (this theorem has no `ArithmeticFP` argument): the two prime
+tests are `hP`, and the inequality of the two values is tested by comparing the two `n`-bit
+words directly (a `pairEq` test: words of equal length have equal values iff they are equal);
+the two range checks `< 2^{max n 2}` are discharged from the fixed widths, not computed (each
+`samplePrimeL` output has `n` bits, so its value is `< 2^n ≤ 2^{max n 2}`,
+`listToNat_lt_two_pow`); the branch is `polyTimeComputable_ite`. The accepted words are
+re-encoded with `max n 2` bits by leading-zero padding (the `max n 2`-bit numeral of an `n`-bit
+word is the word preceded by `max n 2 − n` zeros, a constant block of unary-polynomial length:
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the default pair is a
+constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
 theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
     PolyTimeComputable samplePairRaw := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/RSA.lean b/TCSlib/Cryptography/Candidates/RSA.lean
index e548ac26..e2379a32 100644
--- a/TCSlib/Cryptography/Candidates/RSA.lean
+++ b/TCSlib/Cryptography/Candidates/RSA.lean
@@ -755,14 +755,26 @@ so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", wh
 event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`, `decodeFin_ofFn`,
 `bitsToNat_natToBits`, `val_units_pow`). Since `x ↦ x^e` pushes uniform to uniform
 (`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the inner probability equals the RSA
-inner probability at `(z, e)`. The law of `(z, e)` under the generator's coins is within
-`rsaGenErr n` of the ideal uniform law on `DistinctPrimes n × Z*_{Φ(N)}`
-(`statClose_samplePrime` with the prime fallback `natToBits n 2` of `samplePrimeL` — run-3
-audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map` through the validity
-test with `uprob_diag` and `one_div_card_primes_le` for the fallback on `p = q`,
-`statClose_rejectBlocksL` for `e` with the acceptance rate of the sampleClose sketch); `StatClose.abs_uprob_sub_le_prod` with the
-auxiliary coins `(y, r)` turns `uexp` over the generator's coins into `uexp` over `z`
-(`uexp_prod`, `uprob_prod`) up to `rsaGenErr n`. -/
+inner probability at `(z, e)`: a number `h(z, e) ∈ [0, 1]` (over `y` and `A`'s coins).
+The exponent group `Z*_{Φ(N)}` depends on `z`, so the generator's law is not compared with one
+uniform product: the comparison is a conditional expectation over `z`. Split the generator's
+coins into the two prime segments and the exponent segment (`rsaGenParams`, `uexp_prod`,
+`uprob_prod`). (i) For each fixed prime pair `z`, the exponent drawn from the exponent segment
+(`sampleUnitL` modulo `Φ(N)`, fallback `1`) is within `e^{-n}` of the uniform element of
+`Z*_{Φ(N)}` (`statClose_rejectBlocksL` with the acceptance rate of the sampleClose sketch), so
+the conditional success at `z` exceeds `g(z) := E_{e uniform}[h(z, e)]` by at most `e^{-n}`
+(`StatClose.abs_uprob_sub_le_prod`, with `(y, r)` as the auxiliary coins). (ii) The law of `z`
+under the two prime segments is within `2 · 2^{-n} + 2n/2^n` of the uniform law on
+`DistinctPrimes n` (`statClose_samplePrime` with the prime fallback `natToBits n 2` of
+`samplePrimeL` — run-3 audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map`
+through the validity test with `uprob_diag` and `one_div_card_primes_le` for the fallback on
+`p = q`); averaging the `[0, 1]`-valued `g` over that law instead of the uniform one costs at
+most that distance (`StatClose.abs_uprob_sub_le_prod` again, with `g(z)` read as a probability
+over the auxiliary coins `ω : Π z', Z*_{Φ(N')} × Z_{N'}^* × A.Coins n` at `ω z`). (iii) Adding
+the conditional exponent error, the inversion probability is at most
+`uexp g + (2 · 2^{-n} + 2n/2^n) + e^{-n} = rsaProb (rsaBreaker A) n + rsaGenErr n`, as
+`rsaProb` is the outer `uexp` over `z` of the inner probability over `(e, y, r)`. No error
+beyond `rsaGenErr n` is needed. -/
 theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
     (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/Rabin.lean b/TCSlib/Cryptography/Candidates/Rabin.lean
index d9c93a07..a0a19227 100644
--- a/TCSlib/Cryptography/Candidates/Rabin.lean
+++ b/TCSlib/Cryptography/Candidates/Rabin.lean
@@ -146,8 +146,12 @@ theorem blumFactoring_of_factoring (hD : BlumDensity) (hF : FactoringAssumption)
 
 /-! ## The symmetry lemma (Claim-62.2) -/
 
-/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`: a square root of `1` different from `±1`
-[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"]. -/
+/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`, for coprime moduli `p`, `q`
+[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"].
+It squares to `1` for all coprime moduli (`crtNegOne_sq`). For primes `p`, `q` it differs from
+`1` when `q` is odd and from `−1` when `p` is odd (`crtNegOne_ne_one`, `crtNegOne_ne_neg_one`),
+so for two odd primes it is a square root of `1` other than `±1`. Coprimality alone does not
+give this: for `p = 2`, `q = 3` it is `5 = −1` in `Z_6`. -/
 noncomputable def crtNegOne {p q : ℕ} (h : p.Coprime q) : (ZMod (p * q))ˣ :=
   (crtUnits h).symm (1, -1)
 
@@ -495,8 +499,9 @@ theorem rabinCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rabinCollection
 /-- The statistical error of the Rabin reductions at parameter `n`: two restricted prime
 samplers and the unit sampler of `rabinFactorer`, the latter counted twice because it enters
 through the factor `2` of the symmetry lemma (`e^{-n}` each: `4e^{-n}`), and the diagonal
-`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` for the `P = |Π_n| − 1 ≥ 2` odd
-primes (`one_div_card_primes_le`) and `1/B ≤ 4n/2^n` for the `B` Blum primes (`BlumDensity`).
+`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` with `P = |Π_n|` the total prime
+count, of which `P − 1 ≥ 2` are odd (`one_div_card_primes_le`), and `1/B ≤ 4n/2^n` for the `B`
+Blum primes (`BlumDensity`).
 
 Repair (run-3 audit P7-3): the diagonal term was `2n/2^n`, which neither the Chebyshev bound
 `2^n ≤ 2n|Π_n|` (odd class: `1/(|Π_n| − 1)`) nor `BlumDensity` (`1/B`) yields; both give
diff --git a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
index 423c20bc..ddae2c96 100644
--- a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
+++ b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
@@ -36,7 +36,8 @@ arguments by the text's monotonicity of `t / log t`.
 
 **Deviation:** [PS10, Theorem 31.3] claims the strict inequality `π(x) > x / (2 log x)` for
 every real `x > 1`; equality holds at `x = 2` (`π(2) = 1`), so the theorem is stated with `≤`,
-for natural arguments `m ≥ 2`. **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
+and for natural arguments `m ≥ 2`, which repairs and restricts the real claim (it fails even with
+`≤` at `x = 3/2`, where `π(x) = 0`). **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
 `x = 1, p = 2`; the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is Mathlib's
 `Nat.pow_factorization_choose_le`. **Deviation:** the density corollary needs `n ≥ 2`
 (`Π_1 = ∅`); the text's "`n`-bit numbers" silently assumes it.
@@ -157,7 +158,9 @@ theorem chebyshev_two_mul (x : ℕ) (hx : 0 < x) :
 `m / (2 log₂ m) ≤ π(m)`.
 
 **Deviation:** stated with `≤` (the text's `>` fails at `m = 2`) and for natural arguments
-`m ≥ 2` (the text's real `x > 1`; `π` is a step function, so nothing is lost).
+`m ≥ 2`. This repairs and restricts the text's claim for every real `x > 1`, which is false even
+with `≤`: at `x = 3/2`, `π(x) = 0 < x / (2 log₂ x)`. The natural-argument form is the one the
+prime-density uses need.
 
 **Proof sketch.** Even `m = 2x`: `chebyshev_two_mul`. Odd `m = 2x − 1 ≥ 3`: `2x` is composite,
 so `π(m) = π(2x) ≥ 2x / (2 log₂(2x))`, and `t ↦ t / log₂ t` is increasing for `t ≥ 3`
diff --git a/TCSlib/Cryptography/NumberTheory/Primality.lean b/TCSlib/Cryptography/NumberTheory/Primality.lean
index e9e0e712..1c496b08 100644
--- a/TCSlib/Cryptography/NumberTheory/Primality.lean
+++ b/TCSlib/Cryptography/NumberTheory/Primality.lean
@@ -41,7 +41,10 @@ The Miller–Rabin test [PS10, §2.6.5] and the prime sampler [PS10, §2.6.6]:
 test reject primes with positive probability; the test draws `α ∈ [1, N−1]` as in the
 standard presentation, matching `|L_N| = N − 1`. Even `N > 2` are rejected outright (the text
 handles only the base case `N = 2`). **Deviation:** [PS10, Theorem 49.14] says "with
-probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case needs `N` odd.
+probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case is proved for odd `N`
+only, as a convenience: for even `N > 2` the liars also lie in a proper subgroup of `Z_N^*` (the
+kernel of `x ↦ x^{N−1}`, which misses `−1` since `(−1)^{N−1} = −1`), and the test rejects even
+`N` outright.
 **Deviation:** `SamplePrime` is truncated to `T` trials (strict PPT with failure `⊥`, D10)
 and tests primality exactly (`Nat.Prime`); with Miller–Rabin in place of the exact test the
 output would only be statistically close to uniform. §2.6.6 (p. 50) misquotes the prime
@@ -386,8 +389,11 @@ private theorem liar_pow_mem {N : ℕ} (hN : 2 < N) {j' : ℕ}
 /-- **Odd composites have few liars** [PS10, Lemma 50.15, second half]: for odd composite
 `N > 2`, `|L_N| ≤ (N−1)/2`, stated as `2 |L_N| ≤ N − 1`.
 
-**Deviation:** the text says `N > 2` composite (oddness is needed) and `<` (the proof gives
-`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14).
+**Deviation:** the text says `N > 2` composite and `<`. The restriction to odd `N` is a
+convenience, not a necessity: for even `N > 2` every liar satisfies `α^{N−1} = 1` while the unit
+`−1` does not (`N − 1` is odd and `−1 ≠ 1`), so the liars again lie in a proper subgroup;
+`uprob_millerRabin_le` rejects even `N` outright and needs only the odd case. The proof gives
+`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14.
 
 **Proof sketch.** ([CLRS09, Theorems 31.38–31.39].) Every liar is a unit (`α^{N−1} = 1`,
 `mrLiar_isUnit`), so it suffices to exhibit a proper subgroup of `Z_N^*` containing every
@@ -859,10 +865,11 @@ private theorem spFind_eq (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool) :
     rfl
 
 /-- **`SamplePrime` is a PPT** [PS10, Lemma 51.17, "in time `poly(n)`"], given a
-polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan,
-AKS or Miller–Rabin): there is a uniform `NUPPT` with coin polynomial `2n² · n` whose
-activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks of
-`n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
+polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan:
+an exact deterministic primality test such as AKS; a bounded-error Miller–Rabin test does not
+compute `hP`'s function exactly): there is a uniform `NUPPT` with coin polynomial `2n² · n`
+whose activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks
+of `n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
 
 **Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` (M3): on the state
 word `⟨1^n, r⟩`, the step `spStep` drops the first `n` bits of the second component
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
index f6c4bc5f..8e81839e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
@@ -39,13 +39,15 @@ and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the erro
 a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
 stated for a protocol and a witness relation without assuming the proof property, which the
 theorems add separately.
-The bound `Lz` is necessary, not only convenient (gate 03e, note 9): the distinguisher runs in
-time polynomial in its input, the encoded view, which contains `z`; with `|z| ≥ 2^n` it could
-invert a one-way permutation on `n`-bit inputs and open the unopened commitments of the
-3-colouring protocol, so computational zero-knowledge would fail for every protocol whose
-hiding is only computational. Read literally, [PS10, Definition 121.2] (every
-`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect. For the same reason
-the distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
+The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
+note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
+encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
+binding commitments by exhaustive search. On a graph with two proper colourings outside one
+colour-permutation orbit, that tells the two real views apart with advantage 1, while the
+simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
+`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
+Protocols with exactly simulable views are not affected. For the same reason the
+distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
 
 **Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
 drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
@@ -307,6 +309,15 @@ def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
     (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
       (S.coinLen (NUPPT.inParam w).length)))
 
+/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
+`inParam w`, argument `inArg w`, empty advice and coins
+`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
+theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
+    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
+      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
+        (S.coinLen (NUPPT.inParam w).length))) :=
+  rfl
+
 /-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
 (for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
 first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
@@ -317,6 +328,41 @@ noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
     attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
   else []
 
+/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
+whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
+attempt `i` if `i < N`, and `[]` otherwise. -/
+theorem retry_eq (S : NUPPT) (w : List Bool) :
+    retry S w =
+      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
+          (NUPPT.inParam w).length then
+        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
+      else [] :=
+  rfl
+
+/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
+`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
+`retry_eq` with it and take the `i < |inParam w|` branch. -/
+theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
+    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
+    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
+  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
+    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
+  rw [retry_eq, h, if_pos hi]
+
+/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
+then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
+rewrite `retry_eq` with it and take the `else` branch. -/
+theorem retry_eq_nil {S : NUPPT} {w : List Bool}
+    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
+  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
+      (NUPPT.inParam w).length :=
+    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
+  rw [retry_eq, h', if_neg (lt_irrefl _)]
+
 /-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.
 
 **Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
index 9869c680..675fa55e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
@@ -71,9 +71,10 @@ lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the chan
 variables `gniShear`), which certifies the repaired statements.
 
 **Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
-moves per iteration (`H`, `b`, `γ`, and an empty verifier message) so that the strict
-prover/verifier alternation of `exec` is respected; the repeated protocols run `|x|`
-iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in `|x|` directly).
+moves per iteration (`H`, `b`, `γ`, and a verifier message, empty except for the final
+verdict) so that the strict prover/verifier alternation of `exec` is respected; the repeated
+protocols run `|x|` iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in
+`|x|` directly).
 
 **Deviation (well-formedness):** the verifiers reject common inputs that are not the
 encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
@@ -552,7 +553,8 @@ noncomputable def giVerifierRep : Strategy where
 
 /-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
 `|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
-an empty verifier message, D8 fixed alternation), `4|x|` messages. -/
+a verifier message, empty except for the final verdict, D8 fixed alternation), `4|x|`
+messages. -/
 noncomputable def giProtocolRep : Protocol where
   P := giProverRep
   V := giVerifierRep
@@ -924,18 +926,20 @@ theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
 `n² ≤ |x|`, so at most `|x|` bits per message, on every instance (ruling G3-3 of gate 03;
 `GI.giProver_length_le`). -/
 theorem giProtocol_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocol.ProverBounded R .var := fun x y r hist _ => GI.giProver_length_le x y r hist
+    giProtocol.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProver_length_le x y r hist
 
 /-- The `|x|`-fold form of `giProtocol_proverBounded` (`GI.giProverRep_length_le`). -/
 theorem giProtocolRep_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocolRep.ProverBounded R .var := fun x y r hist _ => GI.giProverRep_length_le x y r hist
+    giProtocolRep.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProverRep_length_le x y r hist
 
 /-- The honest graph non-isomorphism prover sends one bit per message (ruling G3-3 of gate 03;
 `GI.gniProver_length_le`), in one iteration and in the `|x|`-fold protocol. -/
 theorem gniProtocol_proverBounded (R : List Bool → List Bool → Prop) :
     gniProtocol.ProverBounded R (.const 1) ∧ gniProtocolRep.ProverBounded R (.const 1) :=
-  ⟨fun x y r hist _ => GI.gniProver_length_le x y r hist,
-    fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
+  ⟨(Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
 
 /-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
 with soundness error `1/2` and efficient prover with respect to `R_iso`
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
index a8918e97..22a93238 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
@@ -318,7 +318,8 @@ theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Ef
       rw [HardcoreBit.uprob_eq_one_of_forall hall]
       norm_num
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProver_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProver_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact gi_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
index 4aeed143..22b293d7 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
@@ -474,7 +474,8 @@ theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVeri
       have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
       linarith
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProverRep_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProverRep_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact giRep_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 23519614..b6f95458 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -37,10 +37,12 @@ last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chap
 are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
 message as the verdict.
 Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
-verifier, prover) is repeated under strict alternation by appending one dummy empty verifier
-message to each iteration, so that every iteration starts with the prover; the fourth move of
-`giProtocolRep` and of `colProtocolRep`, and the filler moves of the sequential repetition of
-[PS10, §7.2.1] in ch. 7, follow this convention.
+verifier, prover) is repeated under strict alternation by giving each iteration one additional
+verifier move, so that every iteration starts with the prover. In `giProtocolRep` and
+`colProtocolRep` that move is the empty message, except for the protocol's final move, which
+carries the verifier's verdict (the verdict convention above). The sequential repetition of
+[PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(|x|)` filler moves of both parties,
+its last filler again carrying the verdict.
 `Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
 activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
 whole random tape; the time is polynomial in the total input length rather than in `|x|`
@@ -331,6 +333,13 @@ of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate.
 def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
   ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length
 
+/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
+`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
+theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
+    π.ProverBounded R B ↔
+      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
+  Iff.rfl
+
 /-- A message bound `B` implies every pointwise larger bound `B'`. -/
 theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
     (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
diff --git a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
index 6b774497..09042140 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
@@ -33,8 +33,9 @@ read as the output string `[false]`, the negligible `ε` quantified before the i
 cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
 polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
 averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
-every pair of random tapes. The parties' efficiency (the text's "p.p.t.") is
-`Strategy.Efficient`, polynomial time in `|x| + |z| + |messages|` (D8), together with a
+every pair of random tapes. The verifier's efficiency (Definition 116.1's "p.p.t.", and the
+prover's for Definition 119.5) is `Strategy.Efficient`, polynomial time in
+`|x| + |z| + |messages|` (D8), together with a
 polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
 convention of ch. 6): in the completeness clause of `InteractiveProof` and
 `InteractiveProofErr` for the completeness witness, and as the field `boundedP`
@@ -43,10 +44,13 @@ witness. The residual deviation is that against a cheating prover the verifier's
 polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
 are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
 message is still complete (the honest messages are untouched) and sound (against `P*` it acts
-as `V` against `P*` with truncated messages, another prover strategy). So the proof systems
-hold only for languages of the text's class IP — undecidable languages such as the halting
-problem, whose computation histories are not polynomially bounded, are excluded — while
-`IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
+as `V` against `P*` with truncated messages, another prover strategy). So `InteractiveProof`
+(and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`)
+holds only for languages of the text's class IP — undecidable languages such as the halting
+problem, whose computation histories are not polynomially bounded, are excluded — the
+explicit-error forms with a large error say little (with `s = 1` the zero-message,
+always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —
+while `IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
 (run-3 audit P9-1). The capping argument is not formalized as a lemma.
 
 ## Main definitions
@@ -111,12 +115,14 @@ on the complete history of the fixed-alternation execution; `P'` ranges over str
 polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
 `uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
 polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
-witness are bounded by `B(|x|)` (the text's p.p.t. prover writes at most `t(|x|)` bits; the
-convention of ch. 6). Against a cheating prover the verifier's work is polynomial in the
-length of the messages it receives, not in `|x|`; because the honest messages are short the
-verifier can be capped to their length without losing completeness or soundness (module
-docstring), so the predicate holds only for languages of the text's class IP. The class `IP`
-is stated with the message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
+witness are bounded by `B(|x|)` (Definition 116.1's prover need not be efficient; bounding its
+messages is the chosen normal form, harmless because a verifier of time `t(|x|)` reads at most
+`t(|x|)` bits of each message; the convention of ch. 6). Against a cheating prover the
+verifier's work is polynomial in the length of the messages it receives, not in `|x|`; because
+the honest messages are short the verifier can be capped to their length without losing
+completeness or soundness (module docstring), so the predicate holds only for languages of the
+text's class IP. The class `IP` is stated with the message-prefix cap `Strategy.ReadsPrefix`
+(run-3 audit P9-1). -/
 structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
   /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
   efficientV : π.V.Efficient
@@ -232,7 +238,7 @@ theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Boo
       ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
   ⟨B, fun x hx =>
     let ⟨y, hy⟩ := hLR x hx
-    ⟨y, fun r hist => hB x y r hist hy, hc x y hy⟩⟩
+    ⟨y, fun r hist => (π.proverBounded_iff R B).1 hB x y r hist hy, hc x y hy⟩⟩
 
 /-! ### Witness relations -/
 
@@ -466,7 +472,7 @@ theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
 theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
     {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
     (npProtocol T p).ProverBounded R p :=
-  fun x y _ _ hxy => hp x y hxy
+  ((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy
 
 /-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
 `R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
diff --git a/TCSlib/Cryptography/ZeroKnowledge/NP.lean b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
index 8ad8b9c0..9e83f76c 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/NP.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
@@ -275,6 +275,7 @@ theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
     {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
     {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
     (π.pullback f w p).ProverBounded R (B.subst p) := by
+  rw [Protocol.proverBounded_iff] at hB ⊢
   intro x y r hist hxy
   rw [PolyExpr.eval_subst, ← h.length_eq x]
   exact hB (f x) (w x y) r hist (h.witness x y hxy)
@@ -674,25 +675,27 @@ scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduc
 one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
 `1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
 efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
+The Levin reduction `LevinReduction L L3COL R R3COL f w p` is part of the conclusion (ruling
+R-03e-r2-1 of gate 03e round 2), so further protocols can be pulled back along the same maps.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
     {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-      (∀ N, N ≤ p.eval N) ∧
+      LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
       EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
       ZK ((colProtocol Com ℓ).pullback f w p) R ∧
       EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
         (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨f, w, p, h⟩ := h3 L R hR
-  exact ⟨f, w, p, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
+  exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
 zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
 from the text's hypothesis, a one-way permutation, there is a commitment scheme
-(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds,
-under NP-hardness of `3COL` with Levin reductions.
+(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds
+(the Levin reduction included), under NP-hardness of `3COL` with Levin reductions.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
@@ -700,7 +703,7 @@ theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
       ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-        (∀ N, N ≤ p.eval N) ∧
+        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
         EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
         ZK ((colProtocol Com ℓ).pullback f w p) R ∧
         EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
@@ -734,7 +737,7 @@ theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → L
         EfficientProverProofErr π L R
           (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
-  obtain ⟨_, _, p, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
+  obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
   exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
index 0d3c8409..8e77b389 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
@@ -301,8 +301,9 @@ noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
   ((sampleIdx 6 3 T r).map perm3Equiv).getD 1
 
 /-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
-rejection trials of `Nat.size m` bits (so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`),
-the index `0` on failure (D10). -/
+rejection trials of `k = Nat.size m` bits (for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds
+with probability `≥ 1/2`; for `m = 0` the sampler returns the default), the index `0` on
+failure (D10). -/
 def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
   ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0
 
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
index e8cb2fe1..84e5e0a0 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
@@ -495,8 +495,9 @@ noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr
     else []
 
 /-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
-per iteration (commitments, edge, openings, empty verifier message; D8 fixed alternation),
-`4|x|²` moves in all, of which the first `4 n|E|` carry the iterations. -/
+per iteration (commitments, edge, openings, and a verifier message, empty except for the final
+verdict; D8 fixed alternation), `4|x|²` moves in all, of which the first `4 n|E|` carry the
+iterations. -/
 noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
   P := colProverRep Com ℓ
   V := colVerifierRep Com ℓ
@@ -607,7 +608,8 @@ theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExp
     ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
       (colProtocolRep Com ℓ).ProverBounded R B := by
   obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
-  refine ⟨B, fun x y r hist _ => hB x y r hist, fun x y r hist _ => ?_⟩
+  refine ⟨B, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => hB x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => ?_⟩
   show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
   simp only [colProverRep]
   split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _
@@ -878,7 +880,8 @@ theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyE
     obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
     refine ⟨B, fun x hx => ?_⟩
     obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
-    exact ⟨encColoring c, fun r hist => hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
+    exact ⟨encColoring c,
+      fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
       fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
   sound := fun x hx P' z => colProtocol_sound hC x hx P' z
   efficientP := colProver_efficient hC.easy ℓ
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
index c233cc12..955948e3 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
@@ -31,9 +31,10 @@ the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → B
 `ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
 simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.
 
-**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT,
-truncated at `n|E|` attempts and outputting `⊥ = []` on failure, which costs the statistical
-term `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
+**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT
+(D8's definition of `ZK`); it makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as
+the text does (Algorithm 128.7, steps 4–5), and the failure costs the text's own term
+`(1 − 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
 rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
 `2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
 `(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
@@ -318,9 +319,9 @@ theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
     (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))
 
 /-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
-128.8, "`S''` fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the attempts use
-disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability `1 - 1/|E|`
-(`uprob_colSimAttemptH_none`). -/
+128.8, "`S'` [sic: `S''`] fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the
+attempts use disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability
+`1 - 1/|E|` (`uprob_colSimAttemptH_none`). -/
 theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
     (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
     uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
@@ -633,8 +634,9 @@ noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyEx
 the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
 after `n|E|` failures; a single attempt if `E = ∅`.
 
-**Deviation (D8):** truncated at `n|E|` attempts (strict PPT) instead of restarting until
-success. -/
+As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|` attempts, then `fail` (`⊥ = []`).
+**Deviation (D10):** `e'` and the colour pair are rejection-sampled from the tape (defaults `0`
+and `(0, 1)`). -/
 noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
     (x z r : List Bool) : List Bool :=
   let B := (colSimBlock ℓ V').eval x.length
@@ -676,9 +678,10 @@ theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComp
 commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
 Inf-4.4).
 
-**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)` and `N ≥ max ((n₀ + 1)², 4^c · 4)`:
-`n := Nat.sqrt N ≥ n₀` (`Nat.le_sqrt`) and `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`), so
-`N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` once `n ≥ 4^c`, whence `|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
+**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
+`n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
+`N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
+`|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
 theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
     Negligible fun N => μ (Nat.sqrt N) := by
   intro c
@@ -719,48 +722,59 @@ there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| 
 advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
 `ε(|x|)`.
 
-**Deviation (D8, D10):** strict PPT simulator truncated at `n|E|` attempts, rejection-sampled
+**Deviation (D8, D10):** strict PPT simulator (D8's definition of `ZK`), rejection-sampled
 `π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
 undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
 composition, [PS10, §7.2.1], out of scope).
 
-**Proof sketch.** Fix `V'` efficient and take `S` from `exists_colSimulator hC.easy`. Fix
-`Lz` and `D`. Let `B` be the hiding reduction machine of Claim-129.d (`colSimRed` at the
-string level): at parameter `n` it carries in its advice the worst instance
-`(x_n, y_n, z_n)` with `|x_n| = n²`, `|y_n| = 2n`, `|z_n| ≤ Lz(n²)` (`NUPPT.exists_withAdvice`
-with the polynomial bound `add (add (mul var var) (mul (const 2) var)) (Lz.subst (mul var var))`),
-the hybrid index `k_n`, `e₀`, `π₀` and `D.advice n²`; its coins are the other attempts' blocks
-and `D`'s coins (`NUPPT.exists_split`); it runs `V'`'s machine and `D`'s machine
-(`NUPPT.exists_seq`, `NUPPT.exists_comp`, `polyTimeComputable_iterateFind` for the attempts,
-`polyTimeComputable_blockMap ℓ` with `hC.easy` for the commitments, `msgAt` projections by
-`polyTimeComputable_iterate_pairFstD`). `hC.multiHiding var B` gives a negligible `ε_B` with
-`distAdv (multiCom Com v ·) (multiCom Com v' ·) (B.distinguisherL n) ≤ ε_B n` for all `n`-vectors
-`v, v'`. Put
-`ε N := N · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N)) + 2 N² (1/4)^N + N² (1/2)^N + (1/4)^N`,
+**Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
+and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
+the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
+on the encoded optional view (`⊥ ↦ []`).
+
+(1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
+uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
+randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
+`decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
+`some ∘ colRealView`.
+
+If `m > 0`:
+(2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
+`(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
+`statClose_sampleColorPair` — the colour-pair analogue of `statClose_samplePerm3`, still to be
+added: the fill ladder's first step, gate 03g review M3 — and `StatClose.prod` over the blocks).
+(3) `uprob_colSimTruncW_eq`.
+(4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
+`distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
+`CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
+With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
+`cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
+(5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
+`distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.
+
+If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
+`0`). For each fixed `π`, `D`'s advantage is the hiding gap of
+`cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`, with `r_V` fixed by `exists_fixCoins`. Average over `π`.
+If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
+from the real tape when `V'.coinLen 0 > 0`.
+
+The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
+because `|z| ≤ Lz(n²)`: this is where the bound `Lz` is used, see the `Defs.lean` module
+docstring), take those whose fixed reduction (either case) has the largest gap on its own
+vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and openings,
+`pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially bounded by
+`hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform machine once
+(`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins (`NUPPT.exists_reparam_advice`,
+`φ n = n²`). Its acceptance probabilities on `multiCom` samples are the fixed reduction's (coin
+transport along `finCongr`). `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a
+`distAdv` at every `n`), so the hiding terms are at most
+`K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.
+
+Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
 negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
-(`C = 1`), `negligible_two_pow_neg` (with `(1/4)^N ≤ (1/2)^N`), `Negligible.add`,
-`Negligible.const_mul`. Now fix `x = encGraph G`, `y = encColoring c` with `c` proper
-(`R3COL`), `|z| ≤ Lz |x|`, `n` the vertex count, `m = |E|`. If `m = 0` the real view is
-`⟨⟨x,z⟩,⟨r_V,[colCommit (π ∘ c) r, []]⟩⟩` and the simulated one has the all-zero colours, so
-`D`'s advantage is at most `ε_B n` by `hC.multiHiding` applied to a machine `B'` built like
-`B` (absorbed into `B` by a case split on `m` in its advice). Otherwise `n ≥ 2` and the chain is:
-(1) the real view with `π = samplePerm3 |x| …` is within `(1/4)^{|x|}` of the view with a
-uniform `π` (`statClose_samplePerm3`, `StatClose.prod` with `StatClose.refl` for the
-randomness and `V'`'s tape, `StatClose.map` by the view encoding; `exec_succ` three times,
-`decGraph_encGraph`, `decColoring_encColoring`, `colProver`/`colVerifier` unfold to
-`colRealView` with `V com r_V := V'.next x z r_V [com]`); (2) `colSim` is `(Option.map enc
-(colSimTrunc … (n m) w)).getD []` with the `t`-th attempt's coins read from the `t`-th block
-(`colCoinSlice`, `colSimBlock`), within `n m ((1/2)^{|x|} + (1/4)^{|x|})` of the same with
-uniform `(e'_t, (a_t, b_t))` (`statClose_sampleEdgeIdx`, the colour-pair analogue of
-`statClose_samplePerm3`, `StatClose.prod` over the blocks); (3) `uprob_colSimTruncW_eq` makes
-that the law of `colSimTruncW`; (4) `exists_colSimRed_ge` with `N := n m` gives `k, e₀, π₀`
-with `distAdv (truncW) (truncH) D' ≤ n m · distAdv (X) (Y) (colSimRed …)`, and
-`colSimRed … = B.distinguisherL n` up to the coin bijection (`acceptProb_comp_equiv`), so
-`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`; (5) `statClose_colSimTruncH` and
-`one_sub_inv_pow_mul_le_exp` give `distAdv (truncH) (some ∘ colRealView) D' ≤ e^{-n}`
-(`distAdv_le_of_statClose`). The triangle inequality for `distAdv` (`abs_sub_le` on the
-acceptance probabilities) sums the five terms, and `Nat.sqrt |x| = n` (`length_encGraph`,
-`Nat.sqrt_eq`). -/
+(`C = 1`), `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is
+`1`. Use the triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
+(`length_encGraph`, `Nat.sqrt_eq`). -/
 theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
     ZK (colProtocol Com ℓ) R3COL := by
   sorry
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index 61fb0276..f6e3c056 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -423,6 +423,8 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.Commitment.multiHiding
 -- Ruling G3-3: bounded honest prover messages in the proof systems.
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.mono
+-- Round 2, finding 2: the reading lemma of `Protocol.ProverBounded`.
+#print axioms TCSlib.Cryptography.Protocol.proverBounded_iff
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.exists_complete
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.pullback
 #print axioms TCSlib.Cryptography.InteractiveProof.exists_accept
@@ -439,6 +441,11 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 -- Ruling G3-4: perfect zero-knowledge with abort implies statistical ZK (error 2^{-|x|}).
 #print axioms TCSlib.Cryptography.AbortRetry.statClose_retry
 #print axioms TCSlib.Cryptography.AbortRetry.exists_retrySimulator
+-- Round 2, finding 2: the reading lemmas of `AbortRetry.attempt` and `AbortRetry.retry`.
+#print axioms TCSlib.Cryptography.AbortRetry.attempt_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_attempt
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_nil
 #print axioms TCSlib.Cryptography.PerfectZKAbort.statZK
 #print axioms TCSlib.Cryptography.PerfectZKAbort.zk
 #print axioms TCSlib.Cryptography.perfectZK_zeroRounds
diff --git a/machine-library-design.md b/machine-library-design.md
index 1dea9731..52be0e2d 100644
--- a/machine-library-design.md
+++ b/machine-library-design.md
@@ -3087,7 +3087,7 @@ and a statement gate before a second consumer is briefed.
 | H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index (their answers `indicator_inputBitLang`/`indicator_inputLenLang`), the stride decoder `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance), the increment/decrement chain `arm_chain`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` were done in the payback (PR #101, landed 2026-10-15): `Codec/Engine`'s `decodeStride_loop` and `incChain`/`decChain` are instances of `boundedDecodeStride_loop` and `arm_chain` | every received ARM customer through its decider bank; `Codec/Engine` (its decoder and chains are instances); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
 | H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius` directly, `ISCountGenCorrect` transitively) |
 | H13 | **The customer machines**, each with its named consumers and its own reachability notion: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |
-| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`) | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round.** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
+| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`); head envelopes `Clean.envelope` (a clean module's heads stay within `B \|arg\|` cells of the origin at every time), `host_call_envelope` (within `t` cells up to time `t` of a call) and `host_clean_envelope` (`host_clean` with the envelope `B \|arg\|` throughout the call), the coarse envelopes from the time bounds and the unit head moves of `Turing.MultiTapeTM.workTapePos_step_le` | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round; head-envelope clauses added 2026-11-06 (gate 03l round 2, finding 1).** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
 
 **The received ARM machinery, H7–H13** (registered 2026-10-14: the ARM fill gate's round 2,
 finding 5; user decision 3). The rows' public contracts, with file and line, are in

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/replay.log =====

# replay 2026-11-06T00:49:44Z HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans; order=replay-order.txt (downstream2.py of the changed modules, DOWN, + audits/pass-shelat/Checks)
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/SAT rc=0 38s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLipton rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily rc=0 13s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UniformTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifier rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSound rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerComplete rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigma rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Meyer rc=0 7s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CookLevin/Hardness rc=0 385s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Tautology rc=0 10s errors=0 sorry=0
TCSlib/Complexity/ClassNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassOracle/SATOracle rc=0 2s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Inclusions rc=0 29s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHard rc=0 12s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBF rc=0 28s errors=0 sorry=21
TCSlib/Complexity/Randomized/Inclusions rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/Reductions rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/PTMEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPOperator rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPAmplify rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPTIMEThreshold rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoin rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoinHalting rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primality rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Matching rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/NPPoly rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/RPExpected rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Yap rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHosts rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHostsClasses rc=0 45s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroP rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPPIT rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPReduce rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 42s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 23s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 8s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 3s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 4s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 125s errors=0 sorry=0
# done 2026-11-06T01:12:45Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/axioms.log =====

# Axiom prints, gate 03 repair batch, HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba, tree /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (after replay.log)
# Input: axrun/all.lean, generated by g03l-ax/axgen.py over every changed .lean file (changed-lean.txt): 549 #print lines (548 names).
# Base comparison: axrun/base.lean (the same list without the 10 new lemmas) against the untouched #203 tree g03l-oleans (read-only; #203 = BASE in Lean code), axrun/base.out.
# Item B's eight simps equations and the three envelope lemmas: axioms-03l.log.

## Comparison (axcmp.py)
HEAD prints: 548; base prints: 538
sorryAx at HEAD: 100 ; at base: 100
non-standard axioms other than sorryAx at HEAD: []
new names: 10
  NEW TCSlib.Cryptography.AbortRetry.attempt_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_attempt ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_nil ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.Candidates.rejectBlocksL_eq []
  NEW TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL ['Quot.sound']
  NEW TCSlib.Cryptography.Protocol.proverBounded_iff ['propext']
  NEW Turing.ModuleHost.Clean.envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_call_envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_clean_envelope ['Classical.choice', 'Quot.sound', 'propext']
changed axiom sets: 0
missing at HEAD: []
TCSlib.Cryptography.zk_proof_of_witnessRelation ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']
TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']

## HEAD output (axrun/all.out)
'Turing.ModuleHost.first_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.live_prefix' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.clean_iff' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.Clean.envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_install' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_emit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.request_budget' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.state_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.entry_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.hostTM_step_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.guard_add' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.host_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_clean_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_eq_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_ofString_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofString_id_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.blocks_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_blocks_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.Easy.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.eval_yaoBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.eval_yaoRounds' depends on axioms: [propext]
'TCSlib.Cryptography.yaoBlocks_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_38_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.weak_to_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.strong_prod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.weak' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_ofString_id_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_strongOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_weakOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_worstCaseOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermFamily.toFunFamily_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exp_neg_le_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.primesPairEquiv_apply_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_card_primes_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_ne_q' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.ext' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.encodeDistinctPrimes_of_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rejectBlocksL_eq' does not depend on any axioms
'TCSlib.Cryptography.Candidates.rejectBlocksL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_rejectBlocksL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.length_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.dlP_lt_two_pow' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow_dlW' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coprime_dlG_dlP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coe_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expDec_expEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEnc_of_expDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expF_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expValid_dlDefaultIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGenFun_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sampleBelowL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index_of_lt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_D' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.SafePrimeValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlAssumption_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.IsGenerator.orderOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_dlog' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlog_expo' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.two_mul_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_one_ne_one_units' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_half_eq_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_mem_QR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sq_eq_pow_two_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_eq_dlBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlBits_pow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_trial_ge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_shiftInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_dlInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.good_instances' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.FullGroupValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.halfPred_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.halfStr_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_hardCore' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.safe_ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.five_le_safe' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.safe_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_QR_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mem_QR_iff_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_eq_of_mem_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.zpowers_eq_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eq_QR_of_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_sqrt_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_sqTo_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_sq_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_of_uprob_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sq_generator' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.eval_ddhLen' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.length_ddhTuple' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ddhExpo_statClose' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.constSelector_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_pos' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egEncRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egEnc_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egDecStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egDecStr_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egSquareGen_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGroupGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGenMachine_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_valid' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_wellFormed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_secure' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inv_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_easy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.modulusBits_eq_fmult' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.factorProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coins_oneCallFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultWeakPoly' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_weakOneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exists_plantFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.samplePairOut_eq_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_samplePairRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_spec' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_collectionFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.collectionFactorer_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mul_inv_val_modEq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaDec_rsaEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEnc_of_rsaDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleUnitL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.N_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.e_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.d_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaN_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaE_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaValid_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaInvRaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rsaGenErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaBreaker' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaBreaker_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaFromFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorer_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_rsaProb' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsa_imp_factoring' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumDistinctPrimes.ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.oddFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_factoring' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabin_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.oddGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_rabinIndexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinMod_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinDec_rabinEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinEval_spec' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rabinErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinFactorer_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumValid.exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sqTo_bijective_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blum_val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumDec_blumEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumInverter_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_mrExp_mul_mrOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_mul_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mem_mrLiars' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.MRLiar.ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.millerRabin_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.statClose_samplePrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.bitsToNat_eq_listToNat' does not depend on any axioms
'TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins' depends on axioms: [propext]
'TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.simulate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_const_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perfectZK_zeroRounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_attempt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.exists_retrySimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.firstHit_map_getD_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.statClose_retry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.uprob_not_ne_nil_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_exp_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.inv_pow_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.refl' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Isomorphic.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.trans' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.isomorphic_permGraph' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.permGraph_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_isomorphic_both' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_honest_reply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraphAt_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraph_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertices_length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertexCount_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Liso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Lniso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_mem_Lniso_of_mem_Liso' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Riso_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.permCoinLen_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_samplePerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_mul_permFailBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_cheat_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_rep_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gni_rep_cheat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_honest_reply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocolRep_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gniProver_next_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_vTapeSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.permCoinLen_le_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_giBitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.exec_repViews' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.length_Vs' depends on axioms: [propext]
'TCSlib.Cryptography.GI.getD_Vs_even' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.getD_Vs_odd' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOf_congr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_prefixLT' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_init_prefixLE' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.prefixLE_last' does not depend on any axioms
'TCSlib.Cryptography.GI.giVerifierRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProtocolRep_outV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.honest_views' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.encodeMsgs_nil' does not depend on any axioms
'TCSlib.Cryptography.Strategy.encodeMsgs_cons' does not depend on any axioms
'TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.Efficient.exists_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.ReadsPrefix.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.moverIsV_true' does not depend on any axioms
'TCSlib.Cryptography.moverIsV_false' does not depend on any axioms
'TCSlib.Cryptography.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.exec_length' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Protocol.proverBounded_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.ProverBounded.mono' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.withV_V' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_P' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_rounds' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_verifierFirst' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_self' does not depend on any axioms
'TCSlib.Cryptography.Protocol.outV_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outP_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.transcript_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_withV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.exists_proverCoins_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.exists_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_witnessLanguage' does not depend on any axioms
'TCSlib.Cryptography.mem_witnessSet' does not depend on any axioms
'TCSlib.Cryptography.WitnessRelation.eq_witnessLanguage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_witnessRelation_of_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.EfficientProverProofErr.efficientProverProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.EfficientProverProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_outV' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_readsPrefix' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_proverBounded' depends on axioms: [propext]
'TCSlib.Cryptography.npProtocol_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NP_subset_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.coinLen_pullback' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.pullback_outV' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.pullback_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_owp_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encGraph_mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_edgeList_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeOf_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.exists_edgeOf_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_eq_some_edgeOf' depends on axioms: [propext]
'TCSlib.Cryptography.edgeAt_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_isSome' does not depend on any axioms
'TCSlib.Cryptography.edgeAt_eq_none_iff' depends on axioms: [propext]
'TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exp_neg_le_inv_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decColor_encColor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encColor_getD_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.padColor_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.sampleEdgeIdx_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeIdxOfMsg_edgeMsg' depends on axioms: [propext]
'TCSlib.Cryptography.edgeIdxOfMsg_lt' does not depend on any axioms
'TCSlib.Cryptography.statClose_samplePerm3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_sampleEdgeIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.msgAt_encodeMsgs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.committedColor_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_bad_edge' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_col_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colWellFormed_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_multiCom_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.R3COL_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_efficientProverProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_interactiveProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.card_colorPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perm3_ext_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colorPairEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.simColorsW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.firstSome_eq_none_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_colSimTruncH' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_hvzk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zeroKnowledgeProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/seal.log =====

## Part 1: consumers of TCSlib.Cryptography.Protocol.ProverBounded (whole files sealed)

TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (2 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:236:22: error: Function expected at
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:470:2: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/NP.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_NP_sealed_control.lean:279:8: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:928:39: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:932:42: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:938:3: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:611:13: error: Application type mismatch: The argument
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:612:2: error: No goals to be solved
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:882:40: error: Function expected at
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_Soundness_sealed_control.lean:322:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_SoundnessRepGI_sealed_control.lean:478:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

## Part 2: new proofs that read another file's definitions (copies in a SealTest namespace)

TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean: Clean.envelope, host_call_envelope, host_clean_envelope
  seal: ofWords stateWord runFrom step
  sealed current: PASS
  control (Clean.envelope with the seam's head position read by `rfl` through `Cfg.ofWords`): FAIL (1 error lines); expected fail: as expected
    ctl: ModuleHost_envelopes_sealed_control.lean:29:89: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/ZeroKnowledge/Defs.lean: attempt_eq, retry_eq, retry_eq_attempt, retry_eq_nil
  seal: firstIdx layout inParam inArg inCoins output coinLen
  sealed current: PASS
  control (the copies plus one `rfl` read of `firstIdx` (seal-active check)): FAIL (1 error lines); expected fail: as expected
    ctl: Defs_AbortRetry_sealed_control.lean:41:45: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/Candidates/DiscreteLog.lean: sampleBelowL_eq_rejectBlocksL
  seal: rejectBlocksL
  sealed current: PASS
  control (the lemma proved by `funext r; rfl`, reading `rejectBlocksL` through its body): FAIL (1 error lines); expected fail: as expected
    ctl: DiscreteLog_sampleBelowL_sealed_control.lean:15:2: error: Tactic `rfl` failed: The left-hand side
  the same control unsealed: PASS (so its sealed failure is due to the seal)


## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/lint.log =====

# Lint (check 4), HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba vs BASE 092083cd10be7a284db4e97fcf42eddb8296edf7 (archive in g03batch/basetree)
# lint.sh: scripts/style_lint.py on the 21 changed .lean files; scripts/campaign_style_lint.py --check8b per directory, filtered to them.
# Normalized diff base -> head (line numbers masked):
#   26c26,27
#   < INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          548 lines; 16 public / 13 private declarations
#   ---
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
#   28,29c29,30
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines > target 600
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines; 44 public / 6 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
#   45,56c46,57
#   < INFO  TCSlib/Cryptography/Candidates/Concrete.lean             561 lines; 39 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines; 65 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  585 lines; 45 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines; 60 public / 4 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines; 47 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines; 85 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines; 96 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
#   58,60c59,61
#   < INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          308 lines; 11 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines > target 600
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines; 30 public / 30 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
#   67c68
#   < WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       10 public def(s) without a lemma beside them (check 8): Efficient, ProverBounded, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   ---
#   > WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   73,86c74,87
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  981 lines; 68 public / 7 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       464 lines; 49 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 544 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines; 23 public / 5 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
#   89,90c90,91
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   94,98c95,99
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations
# => no new WARN/FAIL; Interaction.lean's check-8 list loses ProverBounded; ModuleHost.lean passes the 600-line target (INFO, 663 lines); the rest are line counts.

### HEAD raw
### scripts/style_lint.py on the changed .lean files

1 findings in 21 files



















TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:723: `colProtocol_sound` proof is 99 lines, no **Proof sketch.**

### scripts/campaign_style_lint.py --check8b, per directory, filtered to the changed files
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
WARN  TCSlib/Cryptography/Asymptotic/OneWay.lean                5 public def(s) without a lemma beside them (check 8): Easy, LengthRegular, OneWayPermutation, strOutLen, yaoRounds
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
FAIL  TCSlib/Cryptography/Candidates/ElGamal.lean              line 749: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 145: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 347: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 532: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 805: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 892: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 927: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 951: `sorry` without a proof sketch in the preceding docstring
WARN  TCSlib/Cryptography/Candidates/Concrete.lean             1 public def(s) without a lemma beside them (check 8): default
WARN  TCSlib/Cryptography/Candidates/DiscreteLog.lean          11 public def(s) without a lemma beside them (check 8): DLAssumption, DLHard, FullLength, FullLengthExcept, SafePrimeValid, WellFormedIndex, dlDefaultIndex, dlG, dlM, expSampleRaw, expUnit
WARN  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  9 public def(s) without a lemma beside them (check 8): FullDLAssumption, FullGroupValid, IsGenerator, dlInverter, dlRoot, halfBit, halfOracle, majOracle, shiftInverter
WARN  TCSlib/Cryptography/Candidates/ElGamal.lean              15 public def(s) without a lemma beside them (check 8): DDHAssumption, Secure, challenge, ddhLen, ddhRandom, ddhReal, ddhTuple, egCanon, egEncParts, egEncRaw, egGenCoins, egGenParts, egGenRaw, egGroupGenRaw, egGroupParts
WARN  TCSlib/Cryptography/Candidates/Factoring.lean            7 public def(s) without a lemma beside them (check 8): FactoringAssumption, fmultBlocks, fmultWeakPoly, plantFactor, prodInverter, samplePairRaw, samplePrimeL
WARN  TCSlib/Cryptography/Candidates/RSA.lean                  19 public def(s) without a lemma beside them (check 8): RSAAssumption, RSAValid, rsaBlock, rsaEncVal, rsaFromFactorRaw, rsaGenCoins, rsaGenErr, rsaGenOut, rsaGenParams, rsaGenRaw, rsaIndexOf, rsaInput, rsaInvRaw, rsaPermAt, rsaSampleCoins, rsaSampleRaw, rsaTrapOf, rsaTrials, unitSampleStr
WARN  TCSlib/Cryptography/Candidates/Rabin.lean                28 public def(s) without a lemma beside them (check 8): BlumDensity, BlumFactoringAssumption, BlumValid, blumDefault, blumEnc, blumEncVal, blumInvNat, blumInvRaw, blumPermAt, blumSampleRaw, oddDefault, rabinEnc, rabinErr, rabinF, rabinFactorRaw, rabinFactorStep, rabinGenCoins, rabinGenOut, rabinGenParams, rabinGenRaw, rabinIndexOf, rabinPrimeCoins, rabinRootRaw, rabinRootStep, rabinSampleRaw, rabinTrials, samplePrimePL, smallDistinctPrimes
INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
WARN  TCSlib/Cryptography/NumberTheory/Primality.lean          6 public def(s) without a lemma beside them (check 8): MRLiar, chunk, listToNat, mrExp, mrLiars, samplePrimeCoins
INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete`
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs`
WARN  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              4 public def(s) without a lemma beside them (check 8): HVZK, PerfectZKAbort, StatZK, ZK
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  12 public def(s) without a lemma beside them (check 8): Liso, Lniso, coinSlice, gniProtocolRep, gniProver, instanceG, instanceG, permFailBound, prefixLE, prefixLT, samplePerm, wellFormedInstance
WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
WARN  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 3 public def(s) without a lemma beside them (check 8): IP, witnessLanguage, witnessSet
WARN  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                1 public def(s) without a lemma beside them (check 8): LevinNPHard
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/statements.txt =====

# Statement diff: decls.py (copied from g03l-fix) over every changed .lean file, BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 vs HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba
# Normalized statement text (comments stripped) of every public declaration, compared by full name.

## Summary: 10 added, 2 changed, 0 removed

## Added
- Turing.ModuleHost.Clean.envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:239)
    theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ} (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
- Turing.ModuleHost.host_call_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:567)
    theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) : ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (t : ℤ)
- Turing.ModuleHost.host_clean_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:642)
    theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ) (h : Clean (M i) f g B) (x arg pre : List Bool) : ∃ t, 0 < t ∧ t ≤ B arg.length ∧ (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state ≠ some (.inl c)) ∧ (hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t = {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧ ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (B arg.length : ℤ)
- TCSlib.Cryptography.Candidates.rejectBlocksL_eq (theorem, TCSlib/Cryptography/Candidates/Concrete.lean:525)
    theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : rejectBlocksL E k B T r = (List.range T).findSome? fun t => if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k)) else none
- TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL (theorem, TCSlib/Cryptography/Candidates/DiscreteLog.lean:476)
    theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) : sampleBelowL m k B T = rejectBlocksL (· < m) k B T
- TCSlib.Cryptography.AbortRetry.attempt_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:315)
    theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) : attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) [] (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take (S.coinLen (NUPPT.inParam w).length)))
- TCSlib.Cryptography.AbortRetry.retry_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:334)
    theorem retry_eq (S : NUPPT) (w : List Bool) : retry S w = if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length < (NUPPT.inParam w).length then attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) else []
- TCSlib.Cryptography.AbortRetry.retry_eq_attempt (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:347)
    theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ} (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ []) (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i
- TCSlib.Cryptography.AbortRetry.retry_eq_nil (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:359)
    theorem retry_eq_nil {S : NUPPT} {w : List Bool} (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = []
- TCSlib.Cryptography.Protocol.proverBounded_iff (theorem, TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:338)
    theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : π.ProverBounded R B ↔ ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

## Changed (both by ruling R-03e-r2-1 (A), item C #4)
- TCSlib.Cryptography.zk_proof_of_witnessRelation (TCSlib/Cryptography/ZeroKnowledge/NP.lean:679->682)
    OLD: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
- TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp (TCSlib/Cryptography/ZeroKnowledge/NP.lean:698->701)
    OLD: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)

## Removed
(none)

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/maintainer-recheck.log =====

# maintainer re-check at 73751f5747d8c0a57aba9939cac8bb16f87ba2ba: 8 key modules, one at a time in import order, on a copy of the worker's tree
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
audits/pass-shelat/Checks rc=0 121s errors=0 sorry=0
# done 2026-11-06T01:22:50Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/base-sync.log =====

# base-sync 2026-11-06T00:22:41Z BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (copy of g03l-oleans, #203 Lean files)
TCSlib/Complexity/Randomized/PPT rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 75s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 10s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 63s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 77s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 10s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 3s errors=0 sorry=0
# done 2026-11-06T00:32:55Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/axioms-03l.log =====

# Gate 03l round 2: axiom prints of the eight simps-generated equations (finding 2) and the new H14 envelope lemmas (finding 1)
# HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba, tree /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans; input axrun/b03l.lean; lean exit 0

#print axioms Complexity.IterateFind.copyTM_k
#print axioms Turing.ModuleHost.hostTM_k
#print axioms Turing.ModuleHost.hostTM_tm_q₀
#print axioms Turing.PairParse.cfg_state
#print axioms Turing.PairParse.cfg_inputPos
#print axioms Turing.PairParse.cfg_workTapes
#print axioms Turing.PairParse.cfg_workTapePos
#print axioms Turing.PairParse.cfg_output
#print axioms Turing.ModuleHost.Clean.envelope
#print axioms Turing.ModuleHost.host_call_envelope
#print axioms Turing.ModuleHost.host_clean_envelope

## Output
'Complexity.IterateFind.copyTM_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.hostTM_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.hostTM_tm_q₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.PairParse.cfg_state' depends on axioms: [propext, Quot.sound]
'Turing.PairParse.cfg_inputPos' depends on axioms: [propext, Quot.sound]
'Turing.PairParse.cfg_workTapes' depends on axioms: [propext, Quot.sound]
'Turing.PairParse.cfg_workTapePos' depends on axioms: [propext, Quot.sound]
'Turing.PairParse.cfg_output' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.Clean.envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_clean_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan, TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan, TCSlib contributors
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clean-module host

A host (`machine-library-design.md` §14, row H14) that runs a finite family of *clean modules*
inside one finite machine.

* **Clean modules.** A clean module (`Turing.ModuleHost.Clean`) is a finite machine with at least
  one work tape that, started at the canonical seam with an argument word as its only
  tape-resident word, halts for the first time at a positive time within a budget of the argument
  length, at the seam holding a result word, having emitted exactly a declared chunk. Every
  polynomial-time word function has a clean **install** module (the value installed as the
  tape-resident word, nothing emitted) and a clean **emit** module (the argument kept, the value
  emitted), each with a polynomial budget (`clean_install`, `clean_emit`). They come from the
  clean-call bridges `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM`, whose modules exit
  at their first positive visit of an exit state: a release flag halts such a module one silent
  step after that visit, and cutting the run at its first halt (`first_halt`) gives the uniform
  contract.
* **The host.** `Turing.ModuleHost.hostTM` pads `n` modules to a shared bank of `K` work tapes
  (all modules share tape 0) and embeds them, through the forwarding transformer
  `Turing.emitAction`, into one finite machine whose states are the host's own control states `C`
  and the modules' states (`Turing.ModuleHost.State C M = C ⊕ Σ i, (M i).State`). When module `i`
  halts, control passes to its return state `ret i`; the control states run a table `ctrl`
  supplied by the consumer (`hostTM_step_inl`). `host_call` and `host_clean` run one module inside
  the host: from the host seam at the module's entry state, with any output prefix, the host
  reaches the seam at the module's return state with the module's result word, forwarding exactly
  the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).

## Origin

Harvested on 2026-11-05 (gate 03l, ruling R-03l-1) from two copies of one private layer: the
module-gluing layer of `TCSlib.Complexity.ClassNP.SAT` on `main` (the streaming emitter behind
`Complexity.SAT_reducible_SAT3` [AB09, Lemma 2.14]: six modules, one control state), and its copy
in pack 03l's `TCSlib.Complexity.Randomized.Build.IterateFindHost` (the repetition machine behind
`Complexity.polyTimeComputable_iterateFind`: five modules, three control states). Both now
instantiate this file; what they vary is a parameter here: the number of modules and their
machines, the control states and their table, the return map and the start state.

## Main definitions

* `Turing.ModuleHost.Clean` — the first-halting clean-module contract (read through `clean_iff`).
* `Turing.ModuleHost.State`, `Turing.ModuleHost.entry` — the host's state type and the entry
  state of a module (`state_eq`, `entry_eq`).
* `Turing.ModuleHost.hostTM` — the host (`hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`).

## Main results

* `Turing.ModuleHost.clean_install`, `clean_emit` — every polynomial-time word function has a
  clean install and a clean emit module with a polynomial budget on the argument length.
* `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
  that no control state is visited; `guard_add` — chaining guarded segments.
* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
  envelopes of a clean module and of a host call.
* `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
  liveness of the prefix of a live run.
* `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
  power.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines; §2.2, the class
  FP; Lemma 2.14, the reduction of the first consumer.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine of the second consumer.)
-/

namespace Turing.ModuleHost

open Complexity

/-! ### Runs: the first halt and the live prefix -/

/-- **The first halt.** If the run of `tm` from a live configuration `cfg` has halted by time
`t`, then it halts for the first time at some time `u` with `0 < u ≤ t`: the configurations
before `u` are live, and the configuration at `u` is the one at `t`.

**Proof sketch.** Take the least halting time `u` (`Nat.find`). It is positive because `cfg` is
live, and since halting is absorbing (`runFrom_of_halt`), the configuration at `t = u + (t - u)`
is the one at `u`. -/
theorem first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- **The live prefix.** If the run of `tm` from `c` is live at time `t`, it is live at every
time `u ≤ t` (halting is absorbing, `runFrom_of_halt`). -/
theorem live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-! ### Clean modules -/

/-- Convert a first-positive-exit module into a halting source: a release flag, raised after
the first step, makes the module halt silently when it is at `exit` — so an entry equal to the
exit still executes once. -/
private def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with
              state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- The release-flag embedding of a module configuration: the flag `b` joins the state, and
every physical field is kept. -/
private def stopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same physical step as the
module and raises the release flag. -/
private lemma stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    simp only [MultiTapeTM.step, stopCfg, hs, Option.map_some]
    simp only [stopTM, hq, ↓reduceIte]
    rfl

/-- Stop a clean call one silent step after its certified first positive exit.

**Proof sketch.** Induct on prefixes, keeping the release flag false only at time zero; the
guard prevents an early stop; the final silent halt keeps every seam field and every emitted
bit. -/
private lemma stop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (stopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := live_prefix C.tm c t
    (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords])
  have hp : ∀ v, v ≤ t → (stopTM C entry exit).tm.runFrom (stopCfg false c) v =
      stopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        stop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = stopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  simp [MultiTapeTM.step, stopTM, stopCfg, Cfg.ofWords, FinTM.controlAction, Action.apply]

/-- **The clean-module contract.** `Clean M result emit B` says: the module `M` has at least one
work tape (`0 < M.k`), and for every native input `x` and argument `arg`, the run of `M` from the
seam at its start state with `arg` as the only tape-resident word halts for the first time at
some time `t` with `0 < t ≤ B |arg|` (every configuration before `t` is live), and the
configuration at `t` is the seam holding the result word `result arg`, with output exactly
`emit arg`. -/
def Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- `Clean M result emit B` holds iff `0 < M.k` and, for every native input `x` and argument
`arg`, some time `t` with `0 < t ≤ B |arg|` is the first halt of `M` from the seam
`Cfg.ofWords M.tm.q₀ (stateWord M.k arg)`, at the seam holding `result arg` with output
`emit arg`. -/
theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) :
    Clean M result emit B ↔ 0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t,
        ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
        {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with
          state := none, output := emit arg} :=
  Iff.rfl

/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
seam at its start state holding `arg` (before, at and after its first halt), every work head is
within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
and the run is constant from `t` on. The contract gives nothing sharper: it fixes the terminal
seam, not the intermediate head positions, and a clean module may move a head out and back
before it halts at the seam (gate 03l round 2, finding 1).

**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
`MultiTapeTM.runFrom_of_halt`). -/
theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
      (B arg.length : ℤ) := by
  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
      none := by
    rw [hend]
  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
    rcases le_total v t with hvt | htv
    · exact ⟨v, hvt, rfl⟩
    · refine ⟨t, le_rfl, ?_⟩
      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
  rw [Cfg.ofWords_workTapePos] at h1 h2
  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
  rw [hu, abs_le]
  constructor <;> omega

/-- Turn a clean-call bridge contract into the uniform first-halting form.

**Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
cutting the run at its first halt (`first_halt`) keeps the whole clean configuration. -/
private lemma clean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    Clean (stopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := stop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := first_halt (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [stopTM, Cfg.ofWords] using hend.trans hs

/-- The bridge overhead `c (A (n+1)^d + n + len + 1) + 1`, with the output length
`len ≤ A (n+1)^d`, fits the single monomial `(c (2A + 1) + 1)(n+1)^{d+1}`.

**Proof sketch.** `n + 1` and both source-time terms are at most multiples of `(n+1)^{d+1}`; the
last unit, which pays for the stop, is at most `(n+1)^{d+1}`. -/
private lemma bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- **Clean install modules.** Every polynomial-time word function `f` has a clean module that
installs `f arg` as the tape-resident word and emits nothing, with a budget `A (|arg| + 1)^d`.

**Proof sketch.** `Turing.FinTM.exists_installCallTM` gives a module that exits at its first
positive visit of an exit state, within `c (T + |arg| + |f arg| + 1)` steps for the source time
`T = A (|arg|+1)^d`; the output length is at most the source time
(`Turing.MultiTapeTM.output_length_le`). The release wrapper and the first-halt cut
(`clean_stop`) give the uniform contract one step later, and `bridge_bound` puts the budget in
the form `A' (|arg| + 1)^{d+1}`. -/
theorem clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise to the source
  -- time before putting it in the uniform argument-length budget.
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **Clean emit modules.** Every polynomial-time word function `f` has a clean module that
keeps its argument as the tape-resident word and emits exactly `f arg`, with a budget
`A (|arg| + 1)^d`.

**Proof sketch.** As `clean_install`, from `Turing.FinTM.exists_emitCallTM`. -/
theorem clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **A common budget.** A polynomial budget `A (m + 1)^d` on a request of length `m` with
`m + 1 ≤ N` is at most `A N^D` for every `D ≥ d` (monotonicity of powers, `0 < N`). -/
theorem request_budget (A d D N m : ℕ) (hd : d ≤ D) (hm : m + 1 ≤ N) :
    A * (m + 1) ^ d ≤ A * N ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans (Nat.pow_le_pow_right (by omega) hd)

/-! ### Padding a module into the shared tape bank -/

/-- Pad an action to a larger tape count, keeping the extra tapes stationary. -/
private def padAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- A module padded into a shared bank of `K` tapes; all modules share tape zero. -/
private def padTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => padAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- The configuration embedding for the shared bank: the padding tapes are blank, with their
heads at the origin. -/
private def padCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with applying an action (the inactive tapes neither write nor move). -/
private lemma pad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (padAction (K := K) a).apply (padCfg c) = padCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply, h]
  · funext i
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply, h]

/-- The padded module runs in lockstep with the module. -/
private lemma pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (padTM M K hk).tm.runFrom (padCfg c) t = padCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, padCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (padCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [padCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (padCfg (K := K) c).state = some q := hs
    simp only [MultiTapeTM.step, hstate, hs]
    change (padAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact pad_apply _ _

/-- With a positive tape count, padding a seam gives the seam with the same state word. -/
private lemma pad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    padCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [padCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [padCfg, Cfg.ofWords, stateWord, hi, hn, FinTM.bufferTape]
  · funext i
    simp [padCfg, Cfg.ofWords]

/-! ### The host -/

/-- The states of the host over the modules `M : Fin n → FinTM Bool` with control states `C`:
`C ⊕ Σ i, (M i).State`, a control state or module `i` in one of its states. -/
abbrev State (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) : Type :=
  C ⊕ Σ i, (M i).State

/-- The host's state type is `C ⊕ Σ i, (M i).State`. -/
theorem state_eq (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) :
    State C M = (C ⊕ Σ i, (M i).State) :=
  rfl

/-- The entry state of module `i` inside the host: module `i` at its start state. -/
def entry {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) : State C M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- The entry state of module `i` is `inr ⟨i, (M i).tm.q₀⟩`. -/
theorem entry_eq {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) :
    entry (C := C) M i = .inr ⟨i, (M i).tm.q₀⟩ :=
  rfl

/-- **The clean-module host** over the modules `M : Fin n → FinTM Bool`: a finite machine with
`K` work tapes (`hk`: every module fits, all modules sharing tape 0), states `State C M`, start
state `q₀`. At a control state `inl c` it applies the consumer's table `ctrl c`; at a module
state `inr ⟨i, s⟩` it applies module `i`'s transition, padded to the `K` tapes and forwarded by
`Turing.emitAction`: the module's emission is the host's, a live successor stays in module `i`,
and a halt passes control to the return state `ret i`. -/
@[simps (config := { isSimp := false }) k tm_q₀]
def hostTM {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) : FinTM Bool where
  k := K
  State := State C M
  tm := {
    q₀ := q₀
    tr := fun q inp work => match q with
      | .inl c => ctrl c inp work
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (ret i)
          ((padTM (M i) K (hk i)).tm.tr s inp work) }

/-- **A control step.** At a configuration in the control state `inl c`, one step of the host
applies the consumer's action `ctrl c` for the scanned input and work symbols. -/
theorem hostTM_step_inl {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) {x : List Bool}
    (cfg : Cfg K Bool (State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
    (hostTM M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  MultiTapeTM.step_of_some hc

/-- Forwarding a padded clean seam produces the host's seam with the supplied output prefix (a
positive tape count identifies the tape-zero word). -/
private lemma host_seam {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (ret : Fin n → State C M) (i : Fin n)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : State C M)) (ret i) pre
      (padCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : State C M))).getD (ret i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := pad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- **A module call inside the host.** Suppose module `i` (with `0 < (M i).k`), run from the seam
at its start state with argument `arg`, is live before time `t` and at time `t` is halted at the
seam holding `result`, with output `out`. Then the host, run from its seam at the entry state of
module `i` holding `arg` with output prefix `pre`, visits no control state before time `t`, and
at time `t` is at the seam in the return state `ret i` holding `result`, with output
`pre ++ out`.

**Proof sketch.** The host seam is the forwarded image (`Turing.emitCfg`) of the padded module
seam (`host_seam`). The module's live run is transferred to the padded machine (`pad_run`) and
then to the host by `Turing.emit_run`, whose agreement hypothesis holds by the definition of
`hostTM`. Every live configuration of the module has a state in module `i`'s summand, hence is
not a control state; the halting endpoint is the forwarded image of the module's terminal seam,
i.e. the host seam at `ret i` (`host_seam` again). -/
theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl c)) ∧
    (hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → State C M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (ret i) pre (padCfg (K := K) c) =
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, entry] using
      host_seam M K ret i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (ret i) pre (padCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (padTM (M i) K (hk i)).tm (hostTM M K hk ctrl ret q₀).tm emb (ret i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [pad_run]
        exact hg u (by omega))]
    rw [pad_run]
  constructor
  · intro v hv a
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg, padCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact host_seam M K ret i hp x result pre out q none

/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
the duration of the call, so this bounds the heads throughout the call.

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
origin, so the host's heads obey any head envelope of the module.

**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
at the origin, and `v ≤ t`. -/
theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
        j| ≤ (t : ℤ) := by
  intro v hv j
  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
    intro c hc
    obtain ⟨h1, h2⟩ :=
      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
    rw [hc] at h1 h2
    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
    rw [abs_le]
    constructor <;> omega
  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)

/-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
from `c` avoids `anchor` before time `a + b`. -/
theorem guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- **A clean module call inside the host.** If module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, and visits no control state before `t`.

**Proof sketch.** Unfold `Clean` for `x` and `arg` and apply `host_call` with the result word
`f arg` and the output `g arg`. -/
theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ :=
    host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- **A clean module call inside the host, with its head envelope** (the bounded call of
`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
every time `v ≤ t` has every work head within `B |arg|` cells of the origin.

The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
the sharper envelope inherited from the module).

**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
`t ≤ B |arg|`, gives the envelope. -/
theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
          v).workTapePos j| ≤ (B arg.length : ℤ) := by
  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB

end Turing.ModuleHost

## ===== machine-library-design.md =====

# Machine-construction library — design document

Status: **FROZEN 2026-10-03** — the open decisions in §9 were resolved by the
user (resolutions recorded inline there). No code exists yet; every Lean
snippet below is an interface *shape*, not a final signature — final
signatures are fixed at spec time and audited.

Evidence base: the epoch-2 checkpoint integration (decision-log row,
2026-10-03). All five open fill frontiers are concrete-machine construction;
147 private helpers were delivered in one epoch, dominated by re-built
copiers, scanners, counters, capture wrappers, and phase glue. The
capture/silence wrapper alone now has four private incarnations
(`universalCaptureTM`, `enumCaptureTM`, `acceptTM`, and the private engine
inside `Composition.lean`'s `exists_cond`).

Prior-art disposition (2026-10-03 discussion): Mathlib's TM2 framework is a
stack-machine model whose poly-time layer contains one machine (the identity)
and no composition theorem; its inter-model compilations are semantics-only.
Decision: build on our own `FinTM` multi-tape model, which owns all the
quantitative assets; adopt the *design idiom* of Mathlib's TM1 statement
language (labelled structured control) for how named machines are written,
import nothing.

## 1. Goals and non-goals

**Goal.** Make "build a finite machine with a proved polynomial time bound"
a library-call activity rather than a bespoke construction, at the
granularity the fill briefs actually need: parse, measure, evaluate a
polynomial, search, split, compare, copy, emit, run a subroutine silently,
branch, loop.

**Non-goals.**
- ~~No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)~~
  **Superseded (user, 2026-10-12): a programming layer is commissioned now
  that the low-level layers are complete; see §15.**
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
  *(The space part is superseded in practice: §12's R3 rows and every later
  framed contract carry space or head-envelope clauses.)*
- No retroactive migration of audited epoch-1/2 proofs (see §8).

## 2. Architecture

Three layers over the existing run calculus:

```
Layer 2  CONTROL      timed cond · loop · capture/silence · halt-redirect
Layer 1  PRIMITIVES   named machines with ComputesFunInTime specs, ABI-compliant
Layer 0  (exists)     run calculus · bufferedCompTM/computesFunInTime_comp ·
                      bufferTape/virtualMove relocation · DecidesInTime
Consumer EXISTENTIAL  PolyTimeComputable / ∈ P corollaries only
```

**Design rule (the bridge lesson).** Constructive layers export *named*
`def` machines plus spec theorems; existential packaging (`∃ M c, …`)
appears only at the consumer layer. Quantifier shape is where audits bite —
a consumer may never need to bound an existential witness.

**Composition stance.** The default sequencing mechanism is *whole-machine*
composition via the public `bufferedCompTM` (already proved, `c = 2`
overhead): chain function machines, don't hand-build phase transitions. The
epoch-2 agents could not do this only because (i) the component machines
didn't exist, (ii) branching has no timed combinator, (iii) loops have no
combinator at all. The library supplies exactly (i)–(iii) and otherwise
stops people from proving phase compositions by hand.

## 3. The calling convention (ABI)

The model already gives whole machines a clean boundary: read-only input
tape, `k` work tapes, write-only (append-only) output tape, start at
`initCfg` with blank work tapes. The ABI therefore governs the only places
where configurations cross a seam *inside* a construction: round boundaries
of the loop combinator and entry/exit of wrapped subroutines.

**Canonical configuration** (the single formal notion, defined once):

- designated *state tapes* hold the round data (specified contents, heads at
  origin);
- all *scratch tapes* are blank with heads at origin;
- the output is empty (nothing emitted yet);
- the control state is a designated live anchor.

Loop bodies and wrappers prove "canonical-in ⟹ canonical-out" lemmas; the
combinators own everything else (startup from `initCfg`, final emission,
fuel exhaustion). Proposed discipline for scratch: **the body restores its
own scratch to blank as part of its contract** (it knows its own footprint,
so the proof is its own invariant run backwards), supported by a generic
`clearTM` primitive that sweeps a length-`m` region in `2m + 2` steps.
Rationale: 2A's killer was a *generic* reset proof; a body-specific restore
is mechanical. The alternative (combinator-driven clearing bounded by the
visited-region lemma in `Sweep.lean`) is recorded as the fallback if
body-restore proves heavier than expected. **[Open decision 9.2]**

**Multi-argument functions.** The ABI for arity > 1 is the existing
`pairEncode` idiom; the codec machines (§4) make it mechanical. No tuple
tapes, no new conventions.

**Deciders.** A decider is a function machine emitting the singleton
indicator (`[true]`/`[false]`), i.e. `DecidesInTime` as it already exists.
The decision layer (§6) builds AND/OR/NOT/guard over that, so `∈ P` goals
decompose without touching configurations.

## 4. Layer 1 — the primitive catalog

Rule of admission: a primitive enters the catalog only with **two named
customers** among the open frontiers (2A controller, 2B `choiceVerifier` +
reverse direction, 2C two verifier memberships, 2D `D-MEM`/`D-WRAP`/`D-EMIT`)
and the E3/E4 briefs. Current cut — 12 entries:

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P1 | `copyTM` | id in `n + 1` | exists (`Composition.lean`) | everywhere |
| P2 | `constTM w` | `fun _ => w` in `\|w\| + 1` | exists | 2D D-EMIT, E4 |
| P3 | `prefixTM w` | `fun x => w ++ x` in `\|w\| + \|x\| + 1` | harvest 2C (promotion already requested) | 2C, 2D D-EMIT |
| P4 | `lengthTM` | `fun x => bits \|x\|` (binary length) | new (2D's counter composition is the engine) | 2B, 2C, 2D D-MEM |
| P5 | `polyEvalTM C c` | `fun x => bits (C·(\|x\|+1)^c)` and unary variant | harvest 2D (`polyUnaryTM` + counter) | 2A startup, 2B, 2C |
| P6 | `pairSplitTM` / `pairJoinTM` | the `pairEncode` codec, both directions | new over existing grammar lemmas (2C/2D parsers are drafts) | 2C, 2D D-MEM/D-WRAP, E4 |
| P7 | `replicateTM` | `fun x => List.replicate (f \|x\|) true` for emitted-count `f` | harvest 2D emission chains | 2D D-EMIT, E4 ledger |
| P8 | `compareTM` | equality / `≤` test of two encoded numbers, singleton verdict | new (small) | 2B, 2C bound re-check |
| P9 | `scanLastTM` | split at last `true` (strip discipline), failure verdict | harvest 2C (`stripCertificate` semantics are proved; machine is new) | 2C, 2B split search |
| P10 | `searchTM` | least `i ≤ n` with `p i`, for `p` decided by a supplied decider on encoded `i` | new (uses W1 + loop L) | 2B split, 2C split |
| P11 | `incrementTM` | fixed-width binary increment + overflow flag + rewind | harvest 2A (`enumCarryTM`) | 2A, E3 padding counters, ch3 |
| P12 | `clearTM` | blank a length-`m` region, `2m + 2` steps | new (trivial) | loop bodies, 2A reset |

Each entry ships as: named `def` + one `ComputesFunInTime`/`DecidesInTime`
spec + an ABI-compliance lemma (canonical-out where applicable). Internal
idiom: TM1-style labelled control (a small inductive of labelled phases with
a `step` match), which is what 2D's `PolyControl` was reaching for.

Harvesting means **reimplementation against the ABI with the original proof
as the template** — the audited originals stay untouched in place; see §8.

## 5. Layer 2 — control

**W1. `captureTM` (silence/capture wrapper).** Given machine `D`: run `D`
with every emission suppressed and recorded — core variant records the full
output on a dedicated capture tape; register corollary extracts the first
bit for deciders. Spec: configuration-preserving lockstep, emission on the
halting transition included (the trap every private build re-proved), return
within `T_D + 1` into a live dispatch state, physical output empty.
Consolidates all four private incarnations; the obligations are already
enumerated by the phase-1 and phase-4 audit tables. **[Open decision 9.3 on
variants]**

**W2. `haltRedirectTM`.** 2C's `acceptTM` pattern as a named transformation:
halt iff captured bit is `b`, else enter the one-state live loop (with its
two-line non-halting lemma). Customers: 2A overflow wiring, HALT-style
control modifications, ch3 diagonalization.

**W3. `condTM` (timed branch).** The timed version of `exists_cond`: given
decider `D` (time `T_D`) and machines `M₁, M₂` (times `T₁, T₂`), a named
machine computing `if p x then f₁ x else f₂ x` within
`c · (T_D + max T₁ T₂ + overhead)`. Engine: W1 + the existing private
capture machinery of `Composition.lean`, made public and timed. Customers:
2C/2D reject-on-malformed guards, every parser.

**L. `loopTM` (the centerpiece — bounded loop with tape-resident state).**
Interface factored from 2A's admitted `enumMachine_contracts`, which is the
validated draft:

```
-- SHAPE ONLY. Final quantifiers to be fixed at spec time, audited.
structure LoopSpec where
  (round data σ, encoded on the state tapes; canonical config family cfg : σ → Cfg)
  (body B; fuel R : ℕ → ℕ; per-round budget T : ℕ → ℕ)
  contract : ∀ s, canonical s →
    within T n, B either EMITS a final verdict and halts,
    or reaches canonical (next s)      -- accept-or-advance
  exhaustion : after R n rounds without emission, halted rejection

theorem loopTM_decides …  :
  (loop machine) decides/computes … within
    startup + R n · (T n + c) + c'
```

The combinator owns: startup from `initCfg` (via an init machine composed
with `bufferedCompTM`), the fuel countdown (P11 as the engine), the final
rejection, and the summation. The body owns: accept-or-advance and its own
scratch restore (§3). 2A's proved `enumLoop_run` is the summation lemma's
template; `enumMachine_contracts` then becomes a *library instantiation*
rather than a bespoke admission. Customers: 2A (directly), P10, 2B reverse
direction, E3 padding, E4 stage loops, ch3 clocked simulation.

**Explicitly deferred from layer 2:** a general tape-embedding transformation
(run a `k`-tape machine on a tape subset of a larger machine). The wrappers
and the loop internally preserve "retained tapes" the way 2A/2B already do;
if a third site needs the general form, it gets designed then — not
speculatively now.

## 6. Decision layer (consumer-facing)

Over `DecidesInTime`: negation, conjunction/disjunction (W1-composition),
`guard` (W3 with constant-reject branch), `decideOfFun` (function machine +
P8-style final test), and the `∈ P` glue through the existing
`mem_P_of_dtime_le`/`mem_P_iff`. Everything here is existential and cheap;
its purpose is that goals like `pairedVerifier C c V ∈ P` decompose into
catalog calls plus the semantic lemmas the agents already proved.

## 7. Placement, naming, policy

- New subdirectory `TCSlib/Complexity/TuringMachine/Build/` (precedent:
  `Robustness/`): `Convention.lean` (ABI notions + canonical-config lemmas),
  `Primitives.lean` (P1–P12; split if the 600-line target demands),
  `Wrappers.lean` (W1–W3), `Loop.lean` (L). Namespace `Turing.FinTM`
  throughout (no new namespace).
- Order list: insert after `Simulation`/`Composition`/`Sweep`, before
  `Encoding` — the library depends only on the run calculus and the public
  relocation/composition machinery; nothing Chapter-1-headline depends on it
  (no import cycles, Chapter-1 statements untouched).
- Attribution: standard constructions, tagged [AB09 §1.2–1.4] where the text
  has them (claim-by-claim as policy requires); module docstring records the
  TM1 statement-language idiom as a design reference (Mathlib) alongside the
  Asperti–Ricciotti and Forster–Kunze precedents.
- This is frozen Chapter-1 surface growth → it gets its own audit (§9.4 for
  the vehicle). Spec statements land sorried first (statement-phase
  discipline), the pack leads with the quantifier shapes (ABI, W1 lockstep,
  L's contract) since that is where this design can be wrong.

## 8. Harvest and migration policy

- Harvest = reimplement against the ABI using the original proof as
  template. Originals (2A/2B/2C/2D privates, audited epoch-1 material) stay
  byte-identical; no re-audit of closed work. **Lifted for the foundation
  migration (user, 2026-10-12): see §16.** Migrated files are rewritten, with a
  freeze check, a replay and a gate for each change.
- Deduplication (retiring privates in favor of library calls) is an **E5
  closure task**, recorded in the backlog, not done opportunistically.
- 2C's pending shared-lemma requests (`prefixTM`/`fixedPair`) are subsumed
  by P3 + P6 and get their disposition in this design's audit round.

## 9. Decisions (resolved by the user, 2026-10-03)

1. **Primitive cut** (§4): P1–P12 confirmed as listed.
2. **Scratch discipline** (§3): body-restores-scratch, with
   combinator-driven clearing via the visited-region bound recorded as the
   fallback if body-restore proves heavier than expected.
3. **Capture variants** (§5 W1): tape-capture core + register corollary.
4. **Audit vehicle**: one shared infrastructure round carrying the library
   spec layer *and* the Chapter-1 bridge export.
5. **Build sequencing**: campaign structure — maintainer writes the spec
   layer serially (quantifier-sensitive), shared audit round, then fills
   dispatched as harvest-adaptation batches, the loop fill flagged for
   continuation budget.
6. **Naming**: `Build/` and the P/W/L working names stand; any rename
   happens before the spec audit (renames after it are drift).

## 9a. Spec-phase refinements (2026-10-03, recorded when the spec layer landed)

The spec layer (`TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean`)
realizes the catalog with these refinements against §4–§5, none touching the
frozen §9 decisions:

- **Seam notion**: `Cfg.ofWords` is a *constructor* (anchor state, input head
  at 1, word-per-tape from the origin via `bufferTape`, heads at origin,
  empty output) and seam contracts are `runFrom`-equations against it —
  rewrite-friendly, and `initCfg` is provably the empty-words seam.
- **Packaging**: contracts are existential in the house idiom of
  `Composition.lean`; fills implement named private machines and close them.
  The §2 named-machine rule is realized as quantifier discipline inside each
  statement (machine fixed after its parameters, before all inputs — the
  bridge lesson), not as global naming.
- **P6** is realized as `pairEncodeFixed` (provably an instance of P3 at the
  doubled-word-plus-separator prefix) plus threaded extractors
  `pairFst`/`pairSnd`/`pairValid`.
- **P7** is subsumed by P5's unary clause, whose instances are what the
  emission customers consume. **P8** is realized in threaded form
  (`pairLenCheck` on `pairEncode a b`, so the original input travels with
  the payload and the audited original-bound re-check is against it).
  **P12** has no standalone contract: clearing is intra-machine, part of the
  loop fill's toolkit.
- **W1** is host-parametric (`captureAction`/`captureCfg` transformers + one
  lockstep equation guarded by source liveness), so consumers embed the
  source into their own controller state type; the register corollary is
  derived at fill time. **W2** is the closed `redirectTM` with an
  `Option Bool` last-emission register (`none` = no emission yet; a source
  with empty output never halts the redirect).
- The lint-mandated construction sketches surfaced a real obligation worth
  recording: append-only output means every parser/extractor must **buffer
  until validity is known** — the output-silence discipline reappears at
  the primitive level (extractors, strip, increment's overflow detection).

## 9b. Round-2 repairs (2026-10-03, after `campaign/gates/ch1-infra/findings.md`)

The round-1 audit refuted `exists_loopTM` (blocker: a zero-step identity
"advance" made the hypotheses vacuous while the conclusion violated the
input-head information bound; major: quantifying rounds over *all* state
words at budget `T |x|` excluded the intended customers) and rejected
disposition D5 (missing dynamic assembly and result-bearing search). The
repairs, all in the spec layer:

**The loop contract, redesigned.** Rounds take positive time (`0 < t`);
rounds are required only on words satisfying an input-indexed
admissibility invariant `Inv x s`, established at `s0` and preserved by
the step; and `stepF`/`acceptF`/payload take the input explicitly (the
enumerator's acceptance runs the verifier on `x ++ s`). Two forms:
`exists_loopTM` (Boolean verdict) and the new `exists_loopFindTM` (first
accepting orbit point's payload; `[]` on exhaustion). The countdown sketch
debits from the **second** anchor entry, so `R = 0` still checks `s0 x`
(round-1 finding 4), and the amortized-borrow budget argument was
validated by the auditor.

**Instantiation tables** (the customer-coverage evidence round 1 asked
for; `m n := C·(n+1)^c` abbreviates the certificate-width polynomial):

| Parameter | Enumerator (2A's `enumMachine_contracts`) | Split search (P10) |
|---|---|---|
| `Inv x s` | `s.length = m x.length` | `s.length ≤ x.length + 1` |
| `s0 x` | `List.replicate (m x.length) false` | `[]` |
| `stepF x s` | `(incFixed s).getD s` (stall on overflow keeps the width) | `if s.length ≤ x.length then s ++ [true] else s` (stall keeps `Inv` step-closed) |
| `acceptF x s` | the captured verifier's verdict on `x ++ s` | `s.length + C·(s.length+1)^e = x.length` |
| payload | — (decision form) | `pairEncode (x.take s.length) (x.drop s.length)`, never `[]` |
| `R n` | `2^(m n) − 1` | `n` |
| fuel bits | `Nat.bits (2^(m n) − 1) = replicate (m n) true` — writable within `T` | `Nat.bits n` — writable within `T` |
| orbit, `i ≤ R n` | all `2^(m n)` width-`m` words, each once (`incFixed` enumeration; the stall is beyond fuel) | the candidates `0, …, n` in unary; `find?` = `solveSplit`'s least solution |
| conclusion shape | `[decide (∃ u, u.length = m n ∧ verifier accepts x ++ u)]` | exactly P10's stated function |

Both invariants bound the state-word length by the input, which is
precisely what dissolves the round-1 finding-2 obstruction (no body is
asked to transform words longer than its budget can traverse).

**Catalog additions** (finding 3): P13 `pairConcat`
(`pairEncode x u ↦ x ++ u`, the D-WRAP shape), P14 `pairDup`
(`x ↦ pairEncode x x`), and the combinator C1 `pairMapSnd` (transform a
pair's payload, retain its head; the data-retaining assembly sequential
composition cannot provide). D-EMIT's nested quadruple then factors as
`pairEncodeFixed α₀ ∘ pairMapSnd (unary-runs generator) ∘ pairDup`, and
D-MEM's parser chains through the extractors with `pairMapSnd` carrying
retained components. **P10 narrowing recorded**: the implemented search is
the fixed length-equation search, not the catalog's supplied-predicate
search; the general form is `exists_loopFindTM` itself.

## 9c. Round-3 repairs (2026-10-03, after `campaign/gates/ch1-infra/findings-r2.md`)

Round 2 passed the redesigned loops, P13/P14/C1, and the §9b tables, and
discharged both round-1 refutations; its one major (finding 1) showed the
loop's *final-answer* conclusion cannot discharge the frozen
`enumMachine_contracts`, which is a *configuration-level* contract — the
auditor's delay machine answers correctly yet violates every per-round
bound. Repairs:

**The configuration-level export.** `exists_loopCfgTM` (same hypotheses
as the decision form) concludes with the host's round-configuration
family: startup ≤ `c·(T+1)` reaching `cfg 0`, empty output at rounds
`0…R`, per-round accept-or-advance segments each within `c·(T+1)`, and
the halted `[false]` terminal at index `R+1`. The decision form becomes a
fill-time corollary through an already-halted-terminal summation lemma
plus monotonicity (R3-1: the frozen `loop_run` requires an empty-output
terminal, so it is not invoked directly on the exported family). **Index/budget
translation to `enumMachine_contracts`** (under the §9b enumerator
instantiation, `w := m n`): candidates `2^w = R n + 1`, so the terminal
index matches; the customer's uniform bound `b·(n + w + 1)^e` dominates
`c·(T n + 1)` once `T` is chosen as a polynomial in `n + w` and `b, e`
absorb `c` and its degree; the per-round indicator matches via the fill's
orbit bridge `(stepF x)^[i] (s0 x) = enumWord w i` (little-endian rank
enumeration, `incFixed` = `enumInc` per the round-2 vocabulary note).

**Vocabulary coefficient shift (round-2 note 5, adopted).** The proved
equalities are `splitAtLastTrue = stripCertificate`, `incFixed = enumInc`,
and `solveSplit (C+1) c = certificateSplit C c` — the split-search
equality is false without the shift (R3-3 corrected this pointer). Consequently the padded-verifier pipeline uses P10 at
`(C + 1, c)` while P8 keeps `(C, c)` for the original witness bound.

**General pairing assembly (round-2 item 10's derivation, adopted
verbatim as the canonical recipe).** For computed `f, g`:
`H x := pairEncode (f x) []` (P14 + C1 at the constant-empty function);
`s x := pairEncode x (H x)`; `t x := pairEncode (s x) (g x)` (P14 + C1,
the second with `g ∘ pairFst`); then
`pairSnd (pairConcat (t x)) = pairEncode (f x) (g x)` — the
self-delimiting grammar makes concatenation-into-payload well-formed at
every stage. A C1 call on `pairEncode a b` computes `g b` only; any
cross-component operation goes through this retained-whole-request
pattern, never through C1 directly (round-2 item 10's D-MEM caveat).

**D5 scope (round-2 items 6/10).** The disposition is re-issued for the
epoch-2 frontiers and P10 only; the E3/E4 rows are component-level
plausibility and their full coverage check is deferred to those epochs'
brief audits, where the six-stage/boundary/ledger tables are in scope.

## 10. Cost and sequencing (estimate, campaign points)

| Work | Est. | Note |
|---|---|---|
| Spec layer (all signatures + ABI) | 8 | maintainer, serial; the design-sensitive part |
| Spec audit round | — | rides with bridge export per 9.4 |
| P1–P12 fills | 14 | mostly harvest-adaptation; parallelizable |
| W1–W3 fills | 9 | W1 obligations already tabulated by past audits |
| L fill | 13 | the real risk concentration; continuation budget anticipated |
| **Total** | **≈ 44** | one mid-size batch equivalent |

Sequencing: freeze this design → spec statements + bridge export → shared
audit round → fills → **then** E2 continuation briefs, which cite the
library instead of re-deriving machines. E2 continuations, E3, E4, and the
ch3 skeleton are the customers that pay this back; the loop combinator is
the piece to watch for slippage.

## 11. The emitter increment (proposed 2026-10-05, post-E3 integration)

**Evidence.** E3's outcome maps the library boundary exactly: everything
recognizer-shaped closed in one round through the catalog (3B's memberships
via `computesFunInTime_splitSolve 1 1` + capture + the audited wrappers; 3D
via P10 + capture + composition), while both stalls sit on the producer
side — 3B at a streaming transducer (`satRedTM` states 9–34, defined,
unproved), 3A at a loop body that must internally run an evaluator and emit
a payload, over a width family the catalog's split instance doesn't cover.
The loop contracts deliberately require **empty output through every round**
(round-2/3 audit repairs), and composition offers only input-pipelining —
there is no output-append mode anywhere in the library. E4's summit
(`SAT_NPHard`, 15 pts, continuation certain) is an emitter of exactly this
shape: a per-index loop appending clause groups under the six-stage
output-silence contract with an exact serialization-length ledger.

**Rule of admission check** (§4): every item below has at least two named
customers among 3B-cont, 4A, 4B, and 3A-cont.

### E1. `emitLoop` — the emitting loop (control layer)

The loop engine's output clause generalized: rounds append exact per-round
emissions instead of staying silent. Shape (final quantifiers at spec time,
audited):

```
-- SHAPE ONLY. Sibling of exists_loopCfgTM, sharing its host machinery.
Inv, s0, stepF as in the decision loop; additionally
  emitF : input → σ → List Bool        -- the exact chunk of round i
contract: startup ≤ c(T+1); per-round segments ≤ c(T+1); positive
  first-return; for every i ≤ R:
    (cfg i).output = (List.range i).flatMap (fun j => emitF x (stepF^[j] s0))
  terminal: halted, output = the full concatenation (no verdict bit — the
  machine COMPUTES the concatenation; a deciding variant is NOT included).
```

Body obligations unchanged (accept-or-advance becomes advance-and-emit;
scratch restore per §3/9.2). The summation lemma is `loop_run`'s template
with the output clause threaded. **Customers:** 4A (the per-snapshot clause
emitter — the design driver), 3B-cont (`satRedTM`'s streaming core as an
instantiation), 4B (dual reduction emitter).

### E2. `emitPhase` — the forwarding wrapper (control layer)

The dual of W1: run an embedded transducer `T` (a `ComputesFunInTime`
contract) inside a host, with `T`'s emissions landing on the **host's**
output tape, source tapes isolated, halt redirected to a live return state;
lockstep lemma in `capture_run`'s mold with "physical output = host prefix
++ T's output so far". This is what lets a catalog transducer serve as one
emission stage of a larger machine — today's only option is whole-machine
input-pipelining. **Customers:** E1's per-round chunk calls (4A emits each
clause group through a sub-transducer), 3B-cont (fresh-literal chain
emission), 3A-cont marginally (the success payload `pairEncode` emission).

### E3′. Stream primitives (catalog rows P16–P18)

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P16 | `tokenStepTM` | consume one self-delimiting token (unary index / marker) from the input head, land head after it, expose the token in control | harvest: 3B's proved `satScanTM`/`satSyntaxStep`, 3D's six-state scan, 2D's parsers (fourth re-derivation otherwise) | 3B-cont, 4A, 4B |
| P17 | `chunkEmitTM w` / parametric | append a control-determined word to output, `\|w\|` steps, no tape movement | new (trivial); the per-token emission atom | E1 bodies, 4A |
| P18 | `unaryAccTM` | dedicated-tape unary accumulator: append one, read-length-in-binary via P4 composition, rewind | harvest: 3B's proved counter stages (`satRedCounter_write`, `satRed_maxOnes`, startup to state 9) | 3B-cont, 4A fresh indices |

### E4′. `splitSolveWith` — width-parametric split search (control layer)

Generalize P15's split search from the hardwired polynomial family to a
hypothesis-supplied width evaluator: given a machine `E` with a captured
`ComputesFunInTime (fun s => bits (f s.length)) T_E` contract and
monotonicity of `n ↦ n + f n`, a machine solving `n + f n = m` (first
success payload `pairEncode (take n) (drop n)`, exhaustion verdict) within
the loopFind envelope over `T_E`. **Harvest source:** 3A-cont's bespoke
body, whose contracts are already displayed in its REPORT — build the
parametric form against that template once it lands (or directly, if this
increment executes first). **Customers:** 3A-cont's equation (plug the
proved `e3_exp_bits_timed`), every future padding argument (ch3+ time
hierarchy pads the same way).

### Placement, cost, open decisions

- **Placement:** E1 extends `Loop.lean` **in-file** to reuse the audited
  `loopHost` privates (a separate `Build/Emit.lean` cannot see them — the
  D7 cross-file-privates qualification; re-deriving the host would be a
  second 2,500-line proof). `Loop.lean`'s size exception grows and the D7
  split trails as already recorded. E2 joins `Wrappers.lean`; P16–P18 join
  `Primitives.lean`; E4′ joins `Loop.lean` beside P15's engine.
- **Non-goals:** no deciding variant of the emitting loop (compose E1 with
  the existing decision layer instead); no general transducer algebra; no
  speculative tape-embedding (unchanged from §5's deferral).
- **Cost estimate:** spec layer 4; one shared-infra audit round (the ch1
  pattern, expected lighter — one host extension, not a new host); fills:
  E1 8, E2 4, P16–P18 5, E4′ 6 — **≈ 27 points**, roughly the L batch.
- **Sequencing:** freeze this section → spec statements → audit round →
  fills → 3B-cont consumes E1/E2/P16–P18; 4A's brief cites the layer
  instead of a bespoke emitter. **3A-cont dispatches in parallel, bespoke**
  (disjoint ownership; its body becomes E4′'s harvest template; later
  dedup is a recorded E5-style maintainer task, never the fill's).
- **Open decisions (user):** (11.1) approve the increment and this scope;
  (11.2) E1 as a sibling contract beside `exists_loopCfgTM` (recommended)
  vs a generalization replacing it (touches audited statements — not
  recommended); (11.3) whether 4A's brief waits for this gate to close
  (recommended) or anticipates it.

## 11a. Spec-phase refinements (2026-10-05, recorded when the emitter spec landed)

Decisions 11.1–11.3 resolved by the user (2026-10-05): increment approved;
E1 is a **sibling** contract beside `exists_loopCfgTM` (no audited statement
is generalized or touched); 4A's brief **waits** for this gate.

Refinements against §11 as drafted, all narrowing:

1. **P17 is subsumed** (no new statement): a constant chunk emission is
   `emitPhase` (E2) applied to the existing P2 `constTM` — recorded here
   the way D4 recorded the prefix/fixed-pair subsumptions.
   *[Superseded by §11b item 6 and §11c: the discharging rule is body
   finite control for fixed words, or `exists_emitCallTM` for computed
   chunks — never the private `constTM` (round-2 audit, finding 3).]*
2. **P18 narrowed to `computesFunInTime_appendBit`**: the drafted
   accumulator row conflated the append atom with cross-phase persistence,
   and persistence is already the loop engine's state-word mechanism; the
   catalog takes only the atom.
3. **E4′ lives in `Primitives.lean`**, not `Loop.lean`: its conclusion
   speaks `pairEncode`, which `Loop.lean` does not import, and P15's own
   public contract already lives there — the engine/contract split follows
   P15 exactly. Its pure vocabulary `solveSplitWith` joins `Convention.lean`
   beside `solveSplit`, which it definitionally generalizes.
4. **E1 is function-level only** (`exists_emitLoopTM` concluding a
   `ComputesFunInTime` of the chunk concatenation): all three named
   customers deliver `PolyTimeComputable` reductions, i.e. function-level
   contracts, and in-host composition of an emitter is E2's job, which
   takes function-level transducers. The round-2 lesson (final-answer vs
   configuration gap) was checked against each customer before choosing
   this form; a configuration-level export would follow the round-3
   precedent if a consumer ever surfaces.
5. **No emission-size hypothesis on E1**: the round seam equality itself
   bounds each chunk by the round's duration (output grows by at most one
   symbol per step), so the statement carries no redundant bound to drift.

Spec surface: **five sorried contracts** (`Turing.emit_run`,
`Turing.FinTM.exists_emitLoopTM`,
`Turing.FinTM.computesFunInTime_splitSolveWith`,
`Turing.FinTM.computesFunInTime_unaryToken`,
`Turing.FinTM.computesFunInTime_appendBit`), two real transformers
(`emitAction`, `emitCfg`), two pure vocabulary definitions
(`solveSplitWith`, `unaryTokenSplit`). Convention's module-docstring
vocabulary bullets extend at fill time (append-only).

## 11b. Round-2 repairs (2026-10-05, after `campaign/gates/emitter-infra/findings.md`)

Round 1: **0 blockers, 2 majors, 3 minors** — no false statement among
the five contracts; both majors are adequacy obligations, repaired here.

1. **The clean-call bridge (finding 1, major).** A function-level
   contract cannot deliver the loop seam: a witness may dirty scratch or
   leave heads displaced on its final transition and still compute `f`
   within `T`. Two new sorried bridge contracts supply the
   prepared-input/clean-return interface, both with canonical
   `Cfg.ofWords`/`stateWord` entry **and** exit seams, first-positive-
   visit discipline, and envelopes charged to `T + |arg| + |f arg| + 1`:
   `Turing.FinTM.exists_installCallTM` (result installed as the
   tape-resident word, nothing emitted) and
   `Turing.FinTM.exists_emitCallTM` (argument preserved, the computed
   chunk forwarded to physical output). Both live in `Loop.lean` beside
   the seams they serve (`stateWord` is defined there). Fill route: the
   A-continuation's proved log/undo pattern around the capture wrapper,
   with virtual-input preparation from the tape-resident argument.
   `emitCfg`'s docstring now states explicitly that it does not
   normalize terminal configurations — the bridges do.
2. **The 3B normalization mapping (finding 1, required resolution).**
   The reported `satRedTM` is **not** the promised instantiation as it
   stands (its permanent position-−1 marker contradicts the blank
   `ofWords` seam; its raw head positions cannot cross seams). The
   committed instantiation plan: loop state word encodes
   `(cursor, consumed-prefix length, phase tag)` via the audited pairing
   vocabulary — the raw streaming position is re-derived each round by
   advancing past the consumed prefix, and **the permanent marker is
   eliminated** (round-local buffering restores its tape by round end).
   Per round: decode the state word; `exists_installCallTM` over
   `computesFunInTime_unaryToken` reads the next token of the remaining
   serialization; finite control classifies marker/polarity bits; the
   emitted clause fragment goes out through `exists_emitCallTM` (chunks
   are of token-bounded length) or directly by finite control for
   fixed fragments; the fresh-variable counter updates through
   `computesFunInTime_appendBit` + install. Rounds have positive
   duration and input-length-only budget; `R` = the serialized input
   length (each round consumes at least one input position); once the
   formula terminator is consumed, an **absorbing finished phase emits
   empty chunks** for all remaining rounds. Token output is decoded by
   `pairDecode`-side vocabulary (proved); append output becomes the
   next state word by the install call. The banked `satReduction_*`
   semantics close the function identity; `satRed_start`'s proved
   maximum-pass survives as the `s0` computation.
3. **The 4A stage mapping (finding 2, required resolution — recorded
   here, certified against the attached phase-4 records in round 2).**
   All-string validation runs **before any irreversible emission**: the
   validation stages run as a decision prefix (the audited conditional
   W3 over the parser/boundary checks); only the valid branch enters
   the emitting loop, and the invalid branch emits the fixed fallback
   through finite control. Logical round count: `R` = the
   snapshot-index bound of the six-stage contract (an input-length-only
   polynomial), one clause group per round through `exists_emitCallTM`;
   the exact serialization-length ledger is the sum of the per-round
   chunk lengths — never constant-per-clause, exactly as the phase-4
   ledger demands. Serialization terminators: the final terminator is
   the last round's chunk tail (or a post-loop constant emission by
   finite control); both options keep the concatenation exact.
4. **Host routing correction (finding 3, minor).**
   `exists_emitLoopTM`'s construction sketch now specifies the
   **forwarding host variant** (body dispatched through `emitAction`;
   fuel/countdown machinery reused; contracts proved over
   arbitrary-accumulated-output configurations; a **new**
   prefix-summation lemma modeled on `loop_run`) — the unchanged
   find-mode host is refuted by the auditor's one-state witness, since
   `captureAction` suppresses the body's physical output.
5. **Token conventions (finding 4, minor).** `unaryTokenSplit`'s
   docstring now states it consumes unary tokens only, with the
   auditor's separating example; standalone markers and polarity bits
   are scanner grammar states.
6. **P17's actual rule (finding 1's visibility note).** Fixed
   finite-control chunks are emitted directly by body control (no
   primitive, no appeal to the private `constTM`); unbounded
   tape-dependent chunks go through `exists_emitCallTM`. §11a item 1 is
   corrected accordingly: the subsumption's discharging rule is body
   finite control, or the emit call, never the private constant
   machine.
7. **Documentation (finding 5, minor).** The four definitions now carry
   customers and construction notes; attestation 4's "every new
   declaration" claim is restated in the round-2 pack as exactly what
   each class of declaration carries.

Spec surface after round 2: **seven sorried contracts** (round 1's five
plus the two bridges), two transformers, two vocabulary definitions.

## 11c. Round-3 repairs (2026-10-05, after `campaign/gates/emitter-infra/findings-r2.md`)

Round 2: **0 blockers, 2 majors, 1 minor** — round-1 findings 3–5 closed;
the bridge construction and the 3B normalization validated (r2 findings
4–5, including a 5,908-case finite corroboration of the normalized
schedule); the two cumulative majors repaired here.

1. **Positive tape count on both bridges (r2 finding 1, major).** At
   `C.k = 0`, `stateWord 0 a = stateWord 0 b` by empty domain, so the
   install conclusion was satisfiable by a two-state zero-tape machine
   for an arbitrary — even noncomputable — `f`: vacuous as a data
   interface. Both conclusions now carry `0 < C.k`, making the seam
   equality yield the genuine `bufferTape` content at index zero. The
   auditor's r2 finding 4 confirms the log/undo construction delivers
   the strengthened interface at the stated envelope.
2. **The 4A mapping rewritten (r2 finding 2, major) — this supersedes
   §11b item 3 in full.** §11b item 3 wrongly substituted parser
   validation for Cook–Levin's silent preparation stages: the 4A source
   is an arbitrary `NP` language, every binary word is a legitimate
   instance, and there is no CNF well-formedness condition on `x` (the
   auditor's empty-language witness: validation-plus-fallback would
   emit the satisfiable `serialize [] = [false]` for a no-instance).
   Parse-before-emission belongs to the 3B/4B decode-based transducers
   only. The corrected stage-to-seam mapping:
   - **Silent preparation (inherited stages s1–s5).** A silent startup
     phase computes and packs the preparation records into `s0 x`:
     exact `Q(n)`, `m = n + Q(n)`, and the horizon `T` (s1, exact
     arithmetic, certificate length never enlarged); the virtual
     reference input `false^m` with clamped virtual head, source
     writes/moves executed on the halting transition, source output
     suppressed and halt internalized (s2–s3, through the capture and
     install-call interfaces at positive tape count); the inclusive
     trajectory records for **all** times `0..T` with administrative
     transitions outside simulated time and frozen positions after an
     early halt (s4); greatest-strictly-earlier-visit records with
     sequential comparison costs (s5). All of s1–s5 end with empty
     physical output and the packed records as the clean persistent
     word — the emitting loop's `s0`.
   - **Ordered emission (s6).** One **family member per round**, the
     cursor walking the fixed family order of the phase-4 contract.
     With `T + 1` snapshot times and `k` work tapes, the six families
     have `n, 1, T, T+1, k(T+1), T` members; the round count is their
     sum: `R = n + (k+3)·T + k + 1` (an input-length-only polynomial).
     Rounds with empty template output still take positive time. The
     single final formula terminator is appended to the last round's
     chunk. The serialization-length ledger is the exact sum
     `1 + 2·#clauses + Σ (v+3)` over literal occurrences — total
     output `O_M(T²)`, never constant-per-clause.
   - The alternative `R = T` time-major grouping is **not** adopted:
     it would need a separate proof that its interleaving reserializes
     to the fixed family order.
   Certification of this mapping against the phase-4 round-2
   boundary-check table is round 3's business — that table
   (`campaign/gates/ch2-phase4-reaudit/findings.md`) rides in the r3 bundle,
   and the 4A brief inherits it verbatim per the standing rule.
3. **P17 cross-reference (r2 finding 3, minor).** §11a item 1 now
   carries an explicit supersession marker pointing at §11b item 6;
   the historical text is preserved as history.
4. **Provenance upgrades for round 3.** The log/undo fill route now has
   fresh in-repo provenance beyond the epoch-2 enumerator: the
   A-continuation checkpoint (integrated 2026-10-05) banked exactly the
   track/clear/compare phase family the r2 finding-4 construction
   describes (`e3cTrackTM`/`e3c_track_run`/`e3cClearTM`/`e3c_clear_run`
   — logged simulation over a visited interval with origin markers,
   exact single-triple cleanup at `6T+7`, positive first returns), as
   proved privates in `Nondeterminism.lean`; its REPORT and source ride
   in the r3 bundle.

Spec surface after round 3: unchanged in count — **seven sorried
contracts** (the two bridges now carrying `0 < C.k`), two transformers,
two vocabulary definitions.

## 11d. Gate close (2026-10-05, after `campaign/gates/emitter-infra/findings-r3.md`)

Round 3: **0 blockers, 0 majors, 1 minor, 4 notes — GATE CLOSED**
(`campaign/gates/emitter-infra/resolutions.md`). Both cumulative majors
discharged: the positive-tape bridges export the data interface (the
auditor's projection-table derivation), and §11c's 4A mapping is
certified against the inherited boundary table, including the exact
per-member chunk rule. The minor — swept in the closing commit — was an
attribution error of §11b item 1/§11c item 4 and the install-call
sketch: the A-continuation's delivered provenance is
**visited-interval tracking and clearing** (`e3cTrackTM`/`e3cClearTM`),
not an overwritten-symbol history/undo implementation; at a clean
entry seam, clearing is restoring, so the track/clear route fills the
bridges directly, and history/undo stands only as the independently
derived alternative (r2 finding 4). Two clarifications from r3
finding 3 bind the 4A brief: `R = n+(k+3)T+k+1` is the last round
index (member count `R + 1`), and the chunk rule emits per-member
flatMaps with the single terminator on the last chunk only. Fill
batches proceed under the resolutions' binding section, partitioned
Loop / Primitives / Wrappers.

## 12. The routine layer (proposed 2026-10-08, pre-ch3/4 campaign)

**Mandate** (user decisions 2026-10-06 and 2026-10-08, recorded in `backlog.md` §2
and `AroraBarakChapters3-4Plan.md` §4a/§8): built after the Chapter-2 closure and
**before the chapter-3/4 fill epochs**, in parallel with their statement phases;
scoped to **amply support the chapter-1/2 retrofit**, not merely the new
consumers; and — superseding §1's "no space bounds" non-goal for this increment —
**every item below carries a space clause alongside its time cost**, so that the
chapter-4 campaign and the P4.x statements consume the layer without a second
pass. The space measure is the house one: `Turing.MultiTapeTM.spaceUsed`
(work-tape cells visited; input and output tapes excluded).

**Evidence.** The 4A chain is the measurement: roughly half of the A2/A3
deliveries' 202 native privates are hand-rebuilt bank/relocation/dispatch
routines; the `emitterBank*`/`emitterP2*` relocation family was privately
re-harvested three times; and A3's proved costs (`3|w| + 3` copy, `2|w| + 2`
clear) match the external prior art's `3w + 2`/`2w + 2` to within one step —
independent convergence on the same catalog, discovered in the 2026-10-06
survey. The emitter round-1 finding stands: *function-level* contracts cannot
deliver clean-return seams, so the gap is configuration-level. §5 deferred the
general tape-embedding transformation "until a third site needs it"; the third,
fourth, and fifth sites have now arrived (the retrofit families, the
Hennie-Stearns conversion, the two-work-tape universal machine).

**What already exists and is consumed, not duplicated** (colleague modules,
Hydroxyi/Jason Dong, on `main` since `f70c57c2`): the *function-level half* —
`TuringMachine/CounterProg{,Run}.lean` (goto programs over unary registers
compiled once into `FinTM`, `t` abstract steps within `t(2t+3)` machine steps,
FP bridge via `ClassNP/CounterProgPolyTime.lean`), `ClassNP/Transducer.lean`,
`ClassNP/{PolyTimePairing,PClosure}.lean`, `TuringMachine/UnaryTape.lean`; and,
on the space side, `SpaceComplexity/Machines/` (the `LogProg` register-program
compiler with `compile_space`/`arm_decides`). §12 supplies the
configuration-level half those layers sit on.

### R1. Bank embedding (the §5 deferral, promoted)

A verified routine on its own `m`-tape set runs on any injectively selected
subset of a `k`-tape host's work tapes, cost unchanged, everything else framed.
Spec shape (final quantifiers fixed at spec time, audited): for an embedding
`ι : Fin m ↪ Fin k`, transported actions and configurations with

* **lockstep** — transported `runFrom` commutes with the source `runFrom`;
* **frame** — tapes outside `range ι` are byte-identical before and after, their
  heads unmoved; input position tracks the source; emission policy is a
  parameter (suppressed or forwarded — the W1/E2 pair fixes the two modes;
  whether this is one transformer with a mode or two transformers is open
  decision 12.4);
* **time** — step count preserved exactly;
* **space** — cells visited on host tape `ι i` equal cells visited on source
  tape `i`; unselected tapes visit nothing new.

Generic form of: `emitterBank*`, the `emitterP2*` relocation family,
`clBank*`/`clSlot*` (4A chain), and their chapter-1 analogues in
`Build/Primitives.lean`/`Build/Loop.lean` internals.

### R2. Seam composition

Sequential composition of two controllers at a canonical `Turing.Cfg.ofWords`
seam (Convention.lean's ABI notion): if `M₁` carries seam `c₀` to seam `c₁`
within `T₁` under a first-return cut, and `M₂` carries `c₁` to `c₂` within
`T₂`, the dispatch-glued machine carries `c₀` to `c₂` within `T₁ + T₂ + O(1)`,
with the glue state-sum and dispatch lemmas owned by the combinator. Space
clause: visited sets union, so per-tape space is bounded by the sum of the
parts' per-tape spaces (whether the spec states the sharper per-tape `max` for
disjointly-owned tapes is open decision 12.1). Generic form of the per-batch
dispatch gluing re-proved in every A-chain and emitter batch.

### R3. Catalog promotion, with space costs

Promotion of the remaining audited A-chain privates as public machines with
exact time *and* space costs: transfer (word from tape `i` to tape `j`,
`3|w| + 3`), copy (`3|w| + 3`), clear (`2m + 2`, = P12's engine), compare, and
increment — D6-style promotion, not new proof work, seeded from the named
private families. Additionally, the existing catalog rows (P1-P12, P16-P18)
and the W/L/E combinators are **retro-annotated with space theorems** — new
`spaceUsed` lemmas beside the existing specs, no signature changes, so the
audited statement surface is untouched (additive growth; open decision 12.3 on
doing this here versus lazily per consumer — the amply-support mandate argues
for here).

### Consumers (rule-of-admission check, §4: two named customers per item)

| Consumer | Uses |
|---|---|
| Chapter-1/2 retrofit (backlog §2) | R1 for the bank/relocation families; R2 for the dispatch families; R3 for `clCopy*`/`clCmp*`/`clRead*`/`clCount*` and the `Build/` harvest families |
| Hennie-Stearns `k`→2 conversion ([AB09] §1.7; ch3-4 plan §2.1) | zones as banks (R1), shifts as R3 transfers, seam discipline (R2); the amortization is mathematics on top |
| Two-work-tape universal machine (ch3-4 plan §2.1, §4a) | R1 + R2 throughout; the retrofit pilot; candidate space-bounded variant feeding Thm 4.8 / Ex 4.1 |
| Chapter-4 ARM extensions (ch3-4 plan §2.5: nondeterministic and polynomial-width variants of `LogProg`) | R1/R2 at their `FinTM` compilation boundary; R3 space rows |

### Placement, sequencing, cost

* New files `Build/Embed.lean` (R1) and `Build/Seam.lean` (R2); R3's new rows in
  a new `Build/Catalog.lean` (`Primitives.lean` is already over the size policy;
  final name is open decision 12.2, settled before the spec audit per §9.6).
  Namespace `Turing.FinTM`; order list after `Build/Loop`.
* Process per `workflow.md`: maintainer-serial spec layer (quantifier-sensitive,
  as §10), statement gate, fills as harvest-adaptation batches, fill audit. The
  gate must close before the first chapter-3/4 fill epoch (plan §4a); statement
  phases of chapters 3-4 run in parallel.
* Estimate (campaign points): R1 spec+fill ≈ 10 (the lockstep is the risk
  concentration, L-style), R2 ≈ 8, R3 promotions + space retro-annotation ≈ 12,
  serial spec layer ≈ 6. Total ≈ 36, one mid-size batch equivalent.

### Open decisions (human review; audit verifies, never disposes)

* **12.1** R2 space accounting — **answered (user, 2026-10-08): the sharper
  form.** The spec states per-tape bounds, with the max for disjointly-owned
  tapes (sharpest available; downstream applications may depend on the
  sharpness).
* **12.2** R3's file layout — **answered (user, 2026-10-08): option (a)**, a
  new `Build/Catalog.lean` holding the new rows and the space lemmas for the
  old rows, keeping `Primitives.lean` byte-identical (**the byte-identity is
  lifted for the §16 migration, user 2026-10-12**); a backlog item records
  the later refactor toward the symmetrical per-theme layout (option (c)),
  via the D7 split window.
* **12.3** Space retro-annotation — **answered (user, 2026-10-08): the refined
  now-option**: the primitives as realized (P1-P15), wrappers (W1-W3) and the
  loop (L) get `spaceUsed` theorems in this increment; the emitter combinators
  (E1-E4′) stay lazy until a space consumer appears, **and the E3′ stream rows
  P16-P18 ride with that lazy scope** (their only consumers are the emitters —
  scope clarification recorded at skeleton time, 2026-10-08, flagged to the
  §12 statement-gate audit and reversible there if the gate reads the
  original "P1-P18" wording as binding).
* **12.4** R1 emission policy — **answered (user, 2026-10-08): two named
  transformers** (suppressing and forwarding) over a shared private core, so
  each spec stays crisp and downstream applications cite whichever fits.

### Citations (policy.md §2, *Design adaptation*)

The configuration-level design is adapted from — with nothing transcribed —
**Édouard Bonnet's `classical-complexity`** (Lax Archive lax-434930), module
`proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`: `StackProgram`'s
`compile_correct`, `StackRename`'s `rename_executes`/`executes_in_sum` (the
bank-embedding and seam-composition shapes), and the
transfer/clear/copy/for/repeat routine catalog; commit
`0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0; examined 2026-10-05,
different toolchain (Lean 4.33 vs our 4.25) and machine model (TM2-style keyed
stacks vs `FinTM` tapes with heads). Suggested tag: `[Bon26]`. The R-modules'
docstrings and their blueprint entries must carry this citation, alongside the
existing `[Balbach22]` (AFP `Cook_Levin`) for the composition architecture and
the in-repo credits to the colleague modules named above.

*Historical (2026-10-14).* `NL_subset_P`'s former sketch cited [Bon26] as design context for
S1b's planned BFS (reachability-table construction; nothing ported). The ARM proof in
`SpaceComplexity/ExpTime.lean` (received `8c23f3bc`) neither uses nor adapts it, and its
docstring drops the tag.

### 12.5 Round-1 audit repairs (2026-10-09)

The §12 statement-gate round 1 (`campaign/gates/routine-infra/findings.md`: 0
blockers, 4 majors) drove four repairs, landed with the round-2 pack:

* **R1 → the returning embeddings** `embedSilentRetTM`/`embedEmitRetTM`
  (states `S ⊕ Unit`): the closed transformers lose a final halting
  emission to either the halt or a premature seam dispatch — the audit's
  formal trace. The returning flavors execute every source action through
  the halting transition and land in the live anchor `Sum.inr ()`.
* **R2 → general-configuration seam composition**
  (`seamCompTM_run_ofCfg` + first-return and visited forms): the canonical
  `Cfg.ofWords` theorems cannot consume arbitrary frames, displaced
  inactive heads, or accumulated output; the general form starts phase two
  from phase one's returned configuration with only the control state
  replaced.
* **R3 → the fresh-entry/release adapter** `seamReleaseTM`: positive
  calls returning to their own anchor are now seam-consumable (the entry
  action executes unconditionally from a fresh start state).
* **R4 → the threaded-map witness** is re-commissioned as a forwarding
  controller (validate/buffer, emit prefix, forward payload output);
  the received captured-payload machine is refuted as a witness for the
  linear-administration bound.

Scope notes R9 (physical-tape selection is not zone multiplexing) and R10
(loop sibling contracts not exported) are recorded at their definition
sites.

### 12.6 Framed catalog contracts (2026-10-10, after ZF-A2's escalation)

**The gap.** The R3 rows (`transferTM`, `copyTM`, `clearTM`, `compareTM`,
`incrementTM`) are stated only from `Cfg.ofWords`: every head at the origin,
every tape a globally buffered word. The zone shift machines (`Build/Zone.lean`,
`exists_zoneShiftInTM`/`OutTM`) have **exactly two tapes**. One is the zoned data
tape; the other is a scratch tape that starts and ends as the unary level word.
Their staging, cleanup and binary navigation counter therefore all run at
**displaced heads beside unrelated data**, where no canonical contract applies.

ZF-A2 (`campaign/fills/zone/reports/f1-A2-REPORT.md`) showed the gap concretely,
with a kernel-checked regression. On a valid three-level carrier, a bare transfer
from a displaced head reads past the word's end and erases a cell that belongs
to the next zone. The cure is a delimited word: blanks at relative positions
`-1` and `|w|`, installed by the consumer, which saves the overwritten cells in
finite control and restores them afterwards. Correspondingly, the contract must
quantify over an arbitrary surrounding frame.

**Decision (user, 2026-10-10).** A small §12 extension: maintainer-drafted
statements, a short statement gate, then a fill batch; ZF-A3 follows. The
routines are local, since each step reads only the scanned cells of the touched
tapes, so a framed contract is the faithful generalization. No new machine is
defined.

**The five statements** (`Build/Catalog.lean`, after the R3 rows, sorried):

| Contract | Exact time | Effect on the touched tapes |
|---|---|---|
| `transferTM_run_ofCfg` | `2·|w| + 2` | source interval blank; destination interval `w` (old destination contents arbitrary) |
| `copyTM_run_ofCfg` | `2·|w| + 2` | destination interval `w`; source intact |
| `clearTM_run_ofCfg` | `2·|w| + 2` | the word interval blank |
| `incrementTM_run_succ_ofCfg` | `2·p + 2`, where `p = (w.takeWhile id).length` | the word interval holds `v`, where `incFixed w = some v` |
| `incrementTM_run_overflow_ofCfg` | `2·|w| + 2` | the word interval all `false` |

In every case the routine reaches its `done` anchor exactly at the stated time
and not earlier. Every cell outside the word intervals, every head, the native
input position and the output are unchanged. Up to the exit the touched heads
stay within `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1,
pos + p]`) and all other heads are fixed. Space bounds follow from the
trajectory clause through `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
`incrementTM`'s carry-sensitive `2p + 2` is the per-step cost that makes the zone
machines' anchored binary countdown sum geometrically, the audited `O(2^i)`
navigation ledger. The canonical `2|w| + 2` public bound is too loose for that,
as ZF-A2 flagged.

**Specialization and dedup.** With the origin heads and globally buffered words
of `Cfg.ofWords`, each framed contract specializes to its canonical R3 row. The
fill batch therefore proves the framed form and **re-derives each canonical row
from it**, through a sanctioned proof-body swap with the public statement
unchanged. That generalizes the private trace lemmas rather than duplicating
them. `compareTM` is not framed here, since no current consumer needs it; it
follows the same pattern on request.

**Pre-ship execution check (mandatory practice).** Every statement was executed
on concrete configurations with displaced heads, a nonblank outer frame and the
edge cases (`w = []`, `p = 0`, all-`true` overflow). The exact final
configuration, the no-earlier-exit clause and the trajectory were compared:
63 cases, all pass, and a wrong-time negative control fails
(`campaign/gates/s12-framed/evidence/`).

### 12.7 Counter-driven loops (design, 2026-10-10, after ZF-B3's escalation; decisions 12.7.1–12.7.6 taken by the user the same day)

**The gap.** ZF-B3 (`campaign/fills/zone/reports/f1-B3-REPORT.md`,
`f1-B3-CONTINUATION.md`) stopped on two shared-interface requests:

- a public fixed-width **decrement** routine with a framed contract;
- a loop whose number of rounds is a **binary counter read from a tape**,
  with the body's state kept on **persistent, arbitrarily positioned tapes**.

Every public loop host (`exists_loopTM`, `exists_loopCfgTM`,
`exists_loopFindTM`, `exists_emitLoopTM`) does something else. It runs
`R x.length` rounds, a count fixed by the input's *length* through a fuel
machine, and every round runs between canonical
`Cfg.ofWords anchor (stateWord …)` seams. A simulator would therefore have to
re-serialize its two simulated work tapes every round, which ZF-B3 rightly
refused.

**This is a shared need, not a ZF-B3 one.**

| Consumer | Status | What it needs |
|---|---|---|
| `Codes2Tape.exists_uniformMachineCode2` | ZF-B3's open target | Simulate at most `t` source steps, `t` in binary on a tape, over two persistent source tapes; one joint polynomial |
| `Diagonalization/EXPCOM.lean` | sorried | The same pattern ("simulate at most `t` source transitions under a binary countdown") |
| `Diagonalization/NTimeHierarchy.lean` | sorried | A **fused** countdown at **linear** overhead: one tick per simulated step, the borrow cost amortized by `Σⱼ ν₂(j) ≤ t` (round-1 finding 5). It needs an **amortized total**, not a per-tick worst case |
| `SpaceComplexity/Hierarchy.lean` | sorried | A configuration-count clock |

**Existing clocks, all private or super-linear.** These are 12.2c candidates
for re-derivation as consumers of the shared host, not inputs to copy:

- `Build/Loop.lean`'s fuel debit: `loopDebit`, `loopValue`, `loopHost_borrow*`.
- `Build/Catalog.lean`'s `f2_loopDebitTM` / `f2_loopBorrow_correct`. This is a
  clean 1-tape little-endian decrement: exact `2·(borrow position) + 2`
  steps, zero wraps to all-`true` with an underflow verdict. It is stated
  only canonically.
- `Universal.lean`'s private deadline interpreter `timedUniversalTM`, the
  quadratic one-tape clock behind `timed_universal`.
- `TimeHierarchy/ClockMachine.lean`'s `clockTM`, the time hierarchy's clock. Its
  specification `clockTM_spec` (`ClockLoop.lean`) is linear in the counter value; "quadratic"
  here was wrong (corrected 2026-10-13, C1 design note): the quadratic bound is
  `timed_universal`'s. These are colleagues' files; under the user's standing preference
  any dedup there is 12.2c work, not theirs.

**Proposed components.**

**C1 — `decrementTM k i : MultiTapeTM k Bool FlagPhase`**, an R3-family row,
the mirror of `incrementTM`. It scans `false` cells to `true` moving right; the
first `true` becomes `false`, with the success verdict; reaching the right
blank, the word is all `false`, so the value is `0`, and the verdict is
underflow, leaving the word all `true`. It returns to the origin through a
`rewind` phase. Framed contracts, in the §12.6 shape:

- `decrementTM_run_succ_ofCfg`, at exact time `2q + 2` where
  `q = (w.takeWhile (· = false)).length`;
- `decrementTM_run_underflow_ofCfg`, at `2|w| + 2`.

The **proof route must not copy the increment proof.** `decrementTM` is
`incrementTM` conjugated by bit complement, so its contracts are derived from
increment's proved framed contracts by a public symbol-complement transport
lemma (decision 12.7.4).

**C2 — `counterLoopTM`, the counter-driven loop host.** Given a body
`B : MultiTapeTM k Bool S` with a re-entry anchor `a`, the host has
`k + 1` tapes, the last one the counter, and states `S ⊕ FlagPhase`.

- At the anchor it runs `decrementTM` on the counter.
- On success it re-enters the body at `a`.
- On underflow it exits to a live `done` anchor.
- If a body round reaches a designated body exit (for a simulator: the
  simulated machine halted), the host exits to a second live `escape`
  anchor.

Its contract `counterLoopTM_run` is stated over **arbitrary configurations**
and has three parts:

- **The body's hypotheses.** A body invariant `P`. A round contract: from any
  `c` with `P c` at `a`, the body reaches, at the exact time `τ c > 0`, either
  the anchor again (with `P`, giving `next c`) or the exit (giving
  `exitCfg c`), without revisiting `a` earlier. And the body never touches the counter
  tape, which the host's embedding enforces.
- **The conclusion.** From the host configuration carrying `c` and a counter
  word `w` of value `d`, delimited:
  - if no round exits early, the host reaches `done` after exactly `d`
    rounds, with body part `next^[d] c` and counter `List.replicate |w| true`;
  - otherwise it reaches `escape` at the first exiting round `r < d`.
- **Total time, exact:** `Σ_{r<d} τ(next^[r] c)` plus the decrement costs
  `Σ_{v=1}^{d} (2ν₂(v) + 2) + (2|w| + 2)` (amortized, at most `4d + 2|w| + 2`)
  plus explicit per-round dispatch constants, fixed when the statements are
  drafted, in the first case; correspondingly in the second. **Uniform-bound
  corollary:** if `τ c ≤ B` whenever `P c`, the total is at most
  `d·B + 4d + 2|w| + O(d)`. Both cases come with no earlier exit and with trajectory
  bounds (counter head within `[pos − 1, pos + |w|]`, body heads as the body's
  own).

C2 is assembled from the §12 layer: the embedding for the body's tape
selection, seams for the anchor/decrement alternation, and the C1 contracts.
No loop-host proof is copied.

**Decisions (user, 2026-10-10).**

1. **Counter placement: a dedicated extra tape**, the host's last tape.
2. **Exits: two live anchors**, `done` and `escape`. A consumer attaches one
   continuation to each with two `seamCompTM` applications, so no new
   composition lemma is needed. A corollary drops the `escape` hypothesis for
   bodies that never exit early. The outermost machine adds its halt once.
3. **Round cost: an exact per-round cost function `τ` of the body
   configuration at the round's start.** The total time is stated exactly as
   the sum over the run's rounds. A round-indexed cost is the special case
   `σ r := τ(next^[r] c)`. A consumer that knows only a bound takes `τ` to be
   the first-return time, which is unique since the contract excludes earlier
   returns. The **uniform bound `B`** is a corollary. This is the
   sensitivity downstream consumers need, for example simulations whose step
   cost grows with tape content.
4. **Decrement proof route: a symbol-complement transport lemma** (option a).
   The §12.6 fill has landed, so increment's framed traces stay as they are.
   The lemma is generic over machines conjugated by a symbol involution, and
   it lives with C1.
5. **Home: a new `Build/CounterLoop.lean`**, importing Catalog, Embed and
   Seam. The 12.2c per-theme reorganization of `Build/` regroups it later.
6. **Scope: the amortized total is stated over the whole run**, not only
   per round.

**Statement phase (2026-10-10).** `Build/CounterLoop.lean` landed with 13
definitions and 10 sorried theorems. The refinements made while drafting:

- **The exit is an `Option S`.** The no-escape corollary is the
  instantiation `exit = none`, so no separate statement is needed.
- **The round hypotheses are stated along the orbit**, not through an
  invariant `P`. This is weaker and so more general; a consumer with an
  invariant derives them.
- **The uniform-bound corollary is pure arithmetic** over the exact time
  (`counterLoop_time_le`). Two amortization lemmas are stated: one for
  prefixes (`4r + 2|w|`) and one for the whole run (`4d + 2|w| + 2`).
- **`decrementTM` is defined as the conjugate** of `incrementTM` by
  `Equiv.boolNot`, through a generic `MultiTapeTM.mapWorkSymbols`. The C1
  contracts are therefore transports of the §12.6 ones.
- **The host has no dispatch steps.** Transitions into the anchor and the
  exit are redirected in place, so the time is exactly the round times plus
  `counterOverhead`.
- **Imports.** Seam is not imported, since consumers compose through
  `seamCompTM_run_ofCfg`. As with `Build/Zone.lean`, the file stays out of
  the `TuringMachine` facade during the statement phase.
- **The counter value** is Mathlib's `Nat.ofDigits 2 (w.map Bool.toNat)`,
  written inline; no new value function is defined.

The executed pre-ship check is `campaign/gates/s12-counter/evidence/`, and the gate
pack is `campaign/gates/s12-counter/{pack,bundle}.md`.

**Statement gate CLOSED (round 1, 2026-10-10: 0 blockers, 0 majors, 1 minor,
5 notes; `campaign/gates/s12-counter/findings.md`).** No false theorem and no missing
soundness hypothesis. Three notes correct or extend this design:

- **SC-4: two continuations need a public prefix lemma.** Two `seamCompTM`
  applications do wire both exits. The escape path through the first
  composite, however, needs the pre-dispatch prefix correspondence, which
  `seamCompTM_run_ofCfg`'s `hexit` cannot provide. The existing private
  `seamComp_left` (`Build/Seam.lean`) proves exactly that. It is to be
  promoted when the first two-continuation consumer is assembled, not copied.
  This corrects decision 12.7.2's claim that "no new composition lemma is
  needed."
- **SC-3: the NTIME consumer needs a nondeterministic lifting.** The host's
  contracts are deterministic (`MultiTapeTM`, `runFrom`). Before the NTIME
  hierarchy fill, a choice-stream lifting contract is needed, with branch
  alignment through the bookkeeping pauses. **Closed (user, 2026-10-13):** C1 takes the
  guess-first route (C1 design note §6, decision 1): the choice word is written first and then
  interpreted deterministically, so no nondeterministic loop host is needed.
  The shared pieces landed with C1 (PR #87, 2026-10-14): the slice lemma in
  `Nondeterministic.lean` (Part A) and the nondeterministic phase host in `Build/NDHost`.
- **SC-5: an optional visited-set corollary.** A public `spaceUsedByTape` or
  visited-set corollary of the trajectory clauses would save the space
  consumers repeated bookkeeping.

Next: the fill batch, after RB5 merges so the host proof can cite the
promoted `MultiTapeTM.runFrom_mapState_of_agreeOn`. ZF-B3's continuation
follows that fill. The existing private
clocks are on the 12.2c tasklist as re-derivation targets (plan §4d,
item 12).


### 12.8 Configuration-graph rows (design draft, 2026-10-10; for the statement phase)

*Drafted from the S1 research (maintainer-commissioned), recorded for the user's decisions 12.8.1–12.8.6. The maintainer's alternative for 12.8.1 is at the end.*

**Why.** The user chose design A for S1b, the summit of `ConfigGraph.lean`:
a configuration-level simulator built on §12 rows (decision log, 2026-10-10).
The S1 research found six capabilities that no public row provides.

| Gap | Missing capability |
|---|---|
| GAP-1 | a native-input-dependent clean seam |
| GAP-3 | a framed compare |
| GAP-4 | a configuration codec with transition application |
| GAP-5 | writing a word at a displaced head |
| GAP-6 | seek over delimited records |
| GAP-7 | two continuations after `counterLoopTM` |

This note proposes reusable rows for all six. Their consumers are every
configuration-graph walker of the campaign:

- S1b (`NSPACE ⊆ DTIME(2^{O(S)})`, hence `NL ⊆ P`);
- Savitch;
- the `PATH` reduction;
- the space hierarchy;
- `TQBF ∈ PSPACE`;
- `NP ⊆ PSPACE`.

**Constraints.**

- (i) **G1** is generalizing `Build/Embed`, `Build/Seam`, Catalog's R3
  sweeps and `FinTM.bufferTape` to `{Symbol : Type*}` in place. A row that
  extends those files' private traces waits for the G1 gate.
- (ii) **G2** (`copyMapTM`/`transferMapTM`) owns the mapped-sweep scanner in
  Catalog. Rows of that family are coordinated with it: one trace per routine
  family.
- (iii) Every row has a framed contract in the §12.6/§12.7 shape (template
  below).
- (iv) The campaign deciders are `FinTM Bool`. `incrementTM`, `decrementTM`,
  `counterLoopTM`, the compare contracts and the Loop hosts stay at `Bool` after
  G1. The record layer is therefore **binary**: decision 12.8.1.

#### Contract template (all rows)

For a tape `i` and a word `w`, write **`Delim d i w`** for the §12.6
hypothesis `∀ p, -1 ≤ p → p ≤ |w| → d.workTapes i (d.workTapePos i + p) =
bufferTape w p`. That is, `w` sits at the head with blanks at `-1` and `|w|`.
Each row `R` states, from any `d` in its start phase:

1. **Exact time** `τ`: `R.runFrom d τ = finish`, where `finish` is `d` with only
   the listed cells and control changed. Every other cell, every head, the
   native input position and the output are unchanged unless the row says
   otherwise.
2. **No earlier exit:** `∀ t < τ, state ≠ done`. (For verdict anchors, this is
   `∀ b`.)
3. **Trajectory:** touched heads stay in a stated interval, typically
   `[pos − 1, pos + |w|]`, and the other heads are fixed. Space follows by
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. That lemma now lives in
   `Build/Catalog.lean` (moved from `Build/Zone.lean` by the B4 pre-issue promotion,
   2026-10-12), so Catalog rows and their consumers can cite it.

The time constants below are indicative. The statement phase fixes them by
the executed pre-ship check, as in §12.6 practice.

Where an exact closed form is unnatural (R8.7's step row), the contract is the
first-return form instead: `∃ t ≤ B`, plus the no-earlier-exit clause.
`counterLoopTM` consumes it with `τ :=` that `t`, which is unique (decision
12.7.3).

#### R8.1 Framed compare (GAP-3)

- `compareTM_run_ofCfg (fst snd) (hne : fst ≠ snd) (u v) (d)
  (hstate : d.state = some .run) (hu : Delim d fst u) (hv : Delim d snd v)`.
  - Exact time `2·δ + 2`, with `δ` the first index where `u` and `v` differ or
    either word ends (`δ ≤ min |u| |v|`, the private `catalog_compare_stop`).
  - Finish: `d` with state `done (decide (u = v))`, every tape unchanged.
  - No earlier `done b`. Trajectory: both heads in `[pos−1, pos+δ]`.
- **Alphabet:** generic with `[DecidableEq Symbol]`. G1 makes `compareTM`'s
  definition generic and keeps its contracts at `Bool`, so the framed row is
  stated generically from the start, and the canonical `compareTM_run` is
  re-derived from it by a sanctioned body swap, exactly as §12.6 did for
  copy/transfer/clear.
- **Trace:** generalize `catalog_compare_trace`, `catalogCompareF` and
  `catalogCompareR` over an outer frame and two start coordinates, on the
  shared `catalog_trace_run` skeleton. No second trace.
- **Home:** `Build/Catalog.lean`, **after the G1 gate**.
- **Note:** a record is a list of blank-separated fields (R8.7), so
  `recordEqTM` is `F` framed compares with R8.3 seeks between them.

#### R8.2 Fold: a finite-state scan with a verdict (new family member)

- `foldTM (i) (δ : A → Symbol → A) (a₀ : A) [Fintype A] [DecidableEq A]`.
  Phases are the forward pass `scan a`, the return `rewind a`, and the anchor
  `done a`.
- `foldTM_run_ofCfg (hw : Delim d i w)`:
  - exact time `2|w| + 2`;
  - finish: `d` with state `done (w.foldl δ a₀)`, all tapes unchanged;
  - no earlier `done`; trajectory `[pos−1, pos+|w|]`.
- **Why a row:** every read of a record field into finite control is a fold.
  That covers the state field, the tag field, "find the marked cell and its
  content and whether it sits at a field end", record validity, and
  acceptance tests. Validators elsewhere (TQBF's well-formedness pass, the
  `PATH` shape checks) are folds too.
- **Alphabet:** generic. **Trace:** `catalog_trace_run` with a read-only
  forward family, as for `copyTM` without the destination. **Home:** Catalog,
  after G1.

#### R8.3 Seek over delimited words and records (GAP-6)

- `skipTM i`: from `Delim d i w`, move right to the word's right delimiter
  and one cell beyond, the next word's first cell. Exact time `|w| + 1`; no
  write; trajectory `[pos, pos+|w|+1]`. `skipBackTM i` is the mirror, starting
  on the cell after the left delimiter of the previous word.
- `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg` have the template shape, with
  the finish `{d with workTapePos i := pos + |w| + 1}`.
- `seekFieldsTM i m` (`m` fixed) composes `m` skips by `seamCompTM_run_ofCfg`.
  `seekEndTM i` skips until the next word is empty (two consecutive blanks);
  it is a fold-guarded loop, under the same skeleton.
- **Consumers:** record navigation (R8.7, S1b's table, Savitch's frame stack),
  and **G4**, which "scans outward across zones, using the separators". Both
  skip blank-separated words, so G4 should cite `skipTM` rather than trace its
  own scan.
- **Trace:** this is the forward half of the R3 trace. Add a forward-only
  sibling of `catalog_trace_run` (`catalog_forward_run`, private), to be shared
  with R8.2's forward phase.
- **Alphabet:** generic. **Home:** Catalog, after G1, **coordinated with G2/G4**.

#### R8.4 Writing words at displaced heads (GAP-5)

- **Computed words** are G2's `copyMapTM`/`transferMapTM` (`merge` and
  `extract`). With `extract := fun _ => b` they fill a blank-free interval with
  a constant (`fillTM i b` is the in-place case `src = dst`, which G2 must
  admit or state separately). Nothing new: G2.
- **Fixed words**: `writeConstTM i (w₀ : List Symbol)` writes the hardwired
  `w₀` from the head and returns.
  - `writeConstTM_run_ofCfg`: exact time `2|w₀| + 1`; finish: cells
    `[pos, pos+|w₀|)` hold `w₀` (old contents arbitrary), head back at `pos`;
    trajectory `[pos, pos+|w₀|]`.
  - The machine is a straight-line chain; its proof uses the public
    `FinTM.emit_run` pattern adapted to writes, so it shares no Catalog trace.
  - **Home:** new `Build/Scan.lean`; **can land now**.
  - **Consumers:** record field initializers (state code, tag code), marker
    cells, per-round patterns inside R8.6's body.

#### R8.5 Native-input rows (GAP-1)

All three are generic over `Symbol`, cite the public `FinTM.rewind_scan` and
`timed_rewind`, and live in new `Build/Scan.lean` (**now**). EmitIterBody's
private startup (`body_start`, `copy_step`, `rwTape_*`, `rwInput_*`) is the
same routine and should be re-derived from `inputCopyTM` in 12.2c T2 (CH7-D2,
coordinated with Aparna).

- `inputCopyTM i`: copy the native input onto tape `i` from the head, then
  rewind both heads.
  - Start: input head at `1`, `Delim`-free destination (old contents
    arbitrary).
  - Exact time `2|x| + c`. Finish: `[pos, pos+|x|)` holds `x`, input head at
    `1`, tape head at `pos`.
  - Trajectory: input head in `[0, |x|+1]`, tape head in `[pos−1, pos+|x|]`.
- `inputLengthTM i`: count `|x|` into a fixed-width binary counter on tape `i`
  (one `incrementTM` per input symbol, cited at its framed carry-sensitive cost).
  - Exact time `Σ_v (2·ν₂(v) + 2) + |x| + c`, amortized at most `4|x| + c`
    (§12.7's potential).
  - Finish: the counter holds `bits |x|` padded to its width, and the input head
    is back at `1`.
  - Bool only, because it uses `incrementTM`. Its home is `Build/CounterLoop.lean`
    or `Scan` importing it.
- `inputSeekTM i c`: move the input head to the binary position `p` held at
  tape `i`.
  - Mechanism: copy `p` to the counter tape `c` (`copyTM_run_ofCfg`), rewind the
    input (`timed_rewind`), then `counterLoopTM` with the one-step body "input
    right".
  - Exact time: the copy (`2|p| + 2`), the rewind (`≤ pos + 2`), then
    `p + counterOverhead w (p + 1)`.
  - Finish: input position `p`, counter tape all-`true` (`counterLoopTM_run_done`).
    Callers clear it (`clearTM_run_ofCfg`).
  - Bool only.
  - **Consumers:** R8.7's input read, `PATH_mem_NL`'s matrix indexing (`u·n + v`),
    virtual-input callers needing random access.
- Packaged combinator **`exists_inputCallTM`** = `inputCopyTM` +
  `exists_installCallTM`: call a function-level machine on the native input at a
  clean seam. It is GAP-1's general form. **Home:** new `Build/InputCall.lean`,
  importing Loop, **now**. It touches no G1 file, but must not collide with
  12.2c T1 item 11's Loop edits.

#### R8.6 Counter-driven expansion

- `expandTM (pat : List Bool)` = `counterLoopTM` around `writeConstTM pat`
  followed by a `skipTM`-like advance. From a counter word of value `d` at the
  counter tape and a blank region on tape `i`, it writes `pat` `d` times
  contiguously.
  - Exact time `Σ_{r<d} τ_pat + counterOverhead w (d+1)`, by
    `counterLoopTM_run_done` and `counterLoop_time_le`.
  - The written word is `pat`ⁿ with `n = d`, which is a framed `Delim` for later
    rows.
- **Consumers:**
  - S1b and Savitch: blank tape fields of `2s+1` cell codes, with `s` given in
    binary by the constructor;
  - `spaceConstructible_logSpace`/`_linear`/`_poly` (binary ↔ unary);
  - the space hierarchy's window radius and clock width (the window route, §16b item 3; the
    budget loop is gone);
  - the §12.7 clocks.
- Bool. **Home:** `Build/CounterLoop.lean` (not G1-owned). **Can land now**,
  once R8.4's `writeConstTM` exists.

#### R8.7 Configuration records (GAP-4)

**Pure layer** (new `Build/CfgRecord.lean`; statements now).

- **Parameters:** a source `M : MultiTapeTM k Bool Q`, `[Fintype Q]`, a window
  radius `s`, an input length `n`, and a finite **tag** type `T` with an update
  `upd : T → Option Bool → T`. The tag carries emission history; the
  configuration graph instantiates `T := OutSummary` and `upd` := the Q1 append
  table. A Build-level row cannot mention `OutSummary`, which is defined
  downstream in `ConfigGraph.lean`; hence the parameter.
- **`cfgRecord n s (c : Cfg k Bool Q x) (τ : T) : List (List Bool)`**, a list of
  `k + 3` **blank-separated fields**, each a blank-free Bool word:
  - **F0** state: a one-hot code of `c.state : Option Q`, width `|Q|+1`;
  - **F1** input position: `c.inputPos` in little-endian binary at the fixed
    width `|bits (n+1)|`;
  - **F2…F(k+1)** tape `i`: `2s+1` three-bit cells
    `(nonblank, value, head-here)` for `z = −s … s`;
  - **F(k+2)** tag: a one-hot code of `τ`.

  Field lengths depend only on `(n, s)`, so records compare field-wise and
  enumerate by counting.
- **`recordTape`** lays the fields out with one blank between fields (and
  between records); the G3 carrier's separator discipline.
- **Window predicate.** `Turing.Cfg.InWindow s` already exists, defined in
  `ClassPSPACE/TQBF.lean`, *downstream* of every Build file. **Decision
  12.8.2:** relocate it verbatim (same name and body) to `CfgRecord.lean` and
  delete TQBF's copy. That is a surface move in a C1d-owned file, so it waits
  for C1d. The alternative is a second predicate under another name, a
  definitional duplicate.
- **`cfgRecord_inj`:** for `InWindow s c` and `InWindow s d` on the same input,
  `cfgRecord n s c τ = cfgRecord n s d τ' ↔ core c = core d ∧ τ = τ'`. It
  follows `ConfigCount.coreCode_inj`.
- **`cfgRecord_valid`:** a word list is a record iff a fold (R8.2) accepts each
  field. One-hot fields, three-bit cells with exactly one head mark per tape
  field, and `F1 ≤ n+1` (the last by `compareTM` against `bits (n+1)` or by
  a fold).

**Rows** (`Build/CfgRecord.lean`). The statements can be drafted now. The
fills need R8.1–R8.3, so they come after the G1 gate.

| Row | Effect (framed; record at the head of tape `r`; scratch tapes blank) | Built from |
|---|---|---|
| `recordReadTM` | Verdict `done (q, ι, σ, τ, edge)`: state, the input symbol at the coded position, the `k` scanned symbols, the tag, and which tape heads sit at a field end. Record unchanged; input head restored | R8.2 folds per field, R8.3 seeks, R8.5 `inputSeekTM` on a copy of F1, `clearTM` |
| `recordApplyTM a` (`a : Action k Bool Q` fixed, `upd` fixed) | Rewrites the record of `c` into that of `a.apply c`, with the tag updated by `a.output`. Per tape it rewrites the marked cell and moves the mark; F1 gets `incrementTM`/`decrementTM` (framed), with the clamp read off the edge data; F0 and the tag go through `writeConstTM`. Precondition: no mark leaves its field (checked by the read) | R8.4, R8.3, Catalog `incrementTM_run_*_ofCfg`, CounterLoop `decrementTM_run_*_ofCfg`, and one local `markShiftTM` per tape field (new, record-specific) |
| **`recordStepTM M upd`** | **The GAP-4 row.** Verdict `done true` with the record of `M.step c` (tag updated) if that configuration is in the window. Verdict `done false` with the record unchanged otherwise, or if `c` is halted (`done true`, unchanged: a halted vertex is its own successor). First-return contract, `t ≤ C_M·(L + n + 1)` with `L` the record length; trajectory inside the record interval and `[0, n+1]` on input | `recordReadTM` ; finite dispatch on `M.tr` ; `recordApplyTM a`, glued by `seamCompTM_run_ofCfg` and two-continuation dispatch (R8.8). An NDTM is consumed per choice bit through `NDTM.fixChoice` (S1a's promotion) |
| `recordInitTM` | Writes the record of `M.initCfg x` with tag `τ₀`, from a radius word (binary `s`) and the input length counter | R8.4, R8.5 `inputLengthTM`, R8.6 `expandTM` |
| `recordEqTM` | Verdict: the two records at the heads of tapes `r`, `r'` are equal | `k + 3` R8.1 compares with R8.3 seeks |
| `recordTestTM P` (`P` a finite predicate on `(state, tag)`) | Verdict `P (c.state, τ)`. Acceptance is `P := (· = none) ∧ (· = accept)` | R8.2 on F0 and the tag field |
| `recordNextTM` | Lexicographic successor among *valid* records (odometer over all field bits, skipping invalid ones), or an overflow verdict | `incrementTM` per field, carry cascade, `recordValidTM` |
| `recordValidTM` | Verdict `cfgRecord_valid` | R8.2 |

**Space.** Every record row is framed inside its record interval plus
`O(L)` scratch. `L = O(k·s + log n + |Q|)`, which is `O(S n)` for Savitch at
`S ≥ logSpace`. This is why F1 is **binary**: a one-hot input track would make
`L = Θ(n)` and break `SPACE(S²)` at `S = log`.

#### R8.8 Two continuations after a two-exit host (GAP-7)

- Promote the existing private `Turing.seamComp_left` (`Build/Seam.lean:173`)
  as **`seamCompTM_runFrom_left`**, statement unchanged. This is SC-4's
  resolution: "expose the existing prefix lemma … do not copy its induction".
- Add one corollary, **`seamCompTM₂_run_ofCfg`**: for a host with two live
  anchors `e₁`, `e₂` (`counterLoopTM`'s `done` and `escape`), nesting two
  `seamCompTM`s attaches a continuation to each. It states the run along
  whichever exit is reached, with the other continuation's summand
  unreachable.
- Generic after G1. **Home:** `Build/Seam.lean`, **after the G1 gate**.
- **Consumers:** every `counterLoopTM` user with an early exit. S1b's BFS
  (queue empty / counter exhausted), the space hierarchy's windowed runner (halt, window
  exit, clock; the window route, §16b item 3), and `recordStepTM`'s internal dispatch.

#### Placement and timing

| Row(s) | Home | Touches a G1-owned file? | When |
|---|---|---|---|
| R8.4 `writeConstTM`; R8.5 `inputCopyTM`, `inputSeekTM`, `inputLengthTM` | new `Build/Scan.lean` (imports CounterLoop) | no | **now** |
| R8.5 `exists_inputCallTM` | new `Build/InputCall.lean` (imports Loop, Scan) | no | **now** (coordinate with 12.2c item 11) |
| R8.6 `expandTM` | `Build/CounterLoop.lean` | no | **now**, after `writeConstTM` |
| R8.7 pure layer, `InWindow` relocation | new `Build/CfgRecord.lean`; `ClassPSPACE/TQBF.lean` | no; TQBF is C1d's | statements now; relocation after C1d |
| R8.1 framed compare; R8.2 fold; R8.3 seek | `Build/Catalog.lean` | **yes** | **after the G1 gate**, with G2 (shared scanner) |
| R8.4 fill (in-place mapped sweep) | Catalog (G2) | **yes** | with G2 |
| R8.8 seam promotion + corollary | `Build/Seam.lean` | **yes** | **after the G1 gate** |
| R8.7 record rows (fill) | `Build/CfgRecord.lean` | no, but cites R8.1–R8.3 | fill after R8.1–R8.3 land |

The process is the house one: maintainer-drafted statements; an executed
pre-ship check (concrete configurations, displaced heads, nonblank outer
frames, `w = []`, `s = 0`, `k = 0`, a halted source); a short statement gate;
fill batches split now/after-G1; a fill gate.

#### Consumers: which rows each walker uses

| Consumer (audited sketch) | Rows |
|---|---|
| **S1b** *(historical: S1b stopped, fills-6; the target is proved at ARM level, §14 H12, 2026-10-14)* `NSPACE_subset_exp_dtime` (BFS; then `NL_subset_P` and Ex 4.3 by the binding route) | R8.7 `recordInitTM`, `recordStepTM` (×2 choice bits), `recordEqTM`, `recordTestTM`; R8.3 table navigation; R8.4/G2 append and counter initialization; R8.6 window fields; R8.8; existing `counterLoopTM`, `embedSilentRetTM_run` (constructor capture), `seamCompTM_run_ofCfg`, `copyTM_run_ofCfg` |
| **Savitch** `savitch` ("frame stack … catalog copy/compare/increment … one extra bank runs the vertex-adjacency test") | `recordStepTM` + `recordEqTM` for `adj(u, v)` (`u = v ∨ step u = v`, both choice bits); `recordNextTM` + `recordValidTM` for the midpoint enumerator; R8.3 seek over the frame stack; `copyTM`/`clearTM` for frame push/pop at **fixed intervals** (note 7); `incrementTM` for the depth field; R8.8 for the recursion's two returns. Space contracts of every row are load-bearing |
| `spaceConstructible_poly`/`_logSpace`/`_linear` | R8.5 `inputLengthTM`; R8.6 `expandTM`; `incrementTM` |
| **`PATH_NLComplete`** hardness (adjacency "by one local transition-table check", logspace) | The sketch's engine is the ARM layer (`arm_decides`). Optionally, a TM route: `recordStepTM`'s space clause with binary F1 gives `O(log n)`-space adjacency deciders for the index languages. Decision 12.8.4 |
| **`PATH_mem_NL`** (matrix indexing) | R8.5 `inputSeekTM` (once a nondeterministic host exists, SC-3; superseded 2026-10-13: C2 is written as programs, §16b item 4) |
| **Space hierarchy** `space_universal`, `space_hierarchy`. **Superseded 2026-10-12 by the window route** (§16b item 3): `space_universal` is forward-only (no interval counters, clock or probe/replay), and `space_hierarchy` runs a self-application universal `U₀` in a window on the record rows | **Now:** R8.7 (`recordInitTM`, `recordStepTM`, `recordTestTM`) under a configuration-count clock (`counterLoopTMVia`), with H2 (step block), H3 (windowed runner, three exits) and H5 (native and binary-position input devices; corrected 2026-10-13: native and the bounded-prefix ruler device, user decisions B1–B2). The earlier route (interval counters, budget loop, R8.8 success/cap exits) is dropped |
| **`TQBF_mem_PSPACE`** (validate-first, depth-first assignment walker, per-clause CNF evaluation) | R8.2 folds (validation, clause evaluation), R8.5 `inputSeekTM` (re-reading prefix bits and matrix bytes), `incrementTM` / a trit odometer (`recordNextTM`'s carry discipline) for the walker, R8.3 seek on the assignment word |
| `NP_subset_PSPACE` | existing `incrementTM` (certificate enumerator) and `vhostEmitTM` (virtual input); R8.8 for accept/exhaust |

#### S1b's machine plan as a composition of these rows

*Historical (2026-10-14): S1b stopped (fills-6), and its target is proved at ARM level (§14 H12).
The rows this plan uses keep one remaining consumer, B6's window route (rows 17–18).*

**Host.** A `FinTM Bool`. It has the native input; the constructor's embedded
tapes plus a capture tape; tape `Tab` (the record table); `Cur₀` and `Cur₁`
(successor workspaces); `Rad` (radius and length words); scratch for
`recordStepTM`; and `Cnt`, the counter, which is the last tape, as
`counterLoopTM` requires.

1. **Radius.** Run `M_S` (from `hS`) under `embedSilentRetTM_run`, with its
   output `bits (S n)` captured, then rewind the input (`timed_rewind`). Its time
   is at most `M_S.configBound n (a·S n)` (`ComputesInTime.of_spaceUsed_le`).
   Multiplying by `c₀` is a fixed binary shift-and-add or `c₀` copies.
2. **Initial table.** Lay down `recordInitTM` (via `inputLengthTM` and
   `expandTM`) on `Tab`, with tag `empty` and a one-bit flag field `[false]`
   ("unprocessed") appended to each record.
3. **Counter.** Copy `Tab`'s first record's fields to `Cnt` contiguously
   (`copyTM_run_ofCfg` + `skipTM`), then fill it with `true` (G2 in-place map).
   Its value `2^{bits(record)} − 1` exceeds the record count `V`, so `done` is
   unreachable before `escape` (or is wired anyway by R8.8).
4. **Round** (the `counterLoopTM` body, anchor `a`). `seekFieldsTM` finds the first
   record whose flag is `false`; if there is none, it reaches the body's exit, and
   the host escapes. Otherwise:
   - copy that record to `Cur₀` and `Cur₁`;
   - run `recordStepTM (N.fixChoice false)` on `Cur₀` and
     `recordStepTM (N.fixChoice true)` on `Cur₁`;
   - for each successor in the window, scan `Tab` with `recordEqTM`, and if it
     is absent, append it at `seekEndTM` with flag `[false]`;
   - set the processed record's flag (`incrementTM` on the one-bit field);
   - clear the workspaces, rewind `Tab` (`skipBackTM` to the table start), and
     return to `a`.

   The round's first-return time `τ` is at most `C·(|Tab| + n + L)` with
   `|Tab| ≤ V·(L + F)`.
5. **Verdict.** From either exit (R8.8), fold `recordTestTM accept` over
   `Tab`'s records and emit `[true]` or `[false]`; then halt (a fixed emission
   tail; `FinTM.emit_run` pattern).
6. **Correctness:**
   - The table is the windowed-reachable set: the BFS invariant, with each record
     identified with a `coreSum` by `cfgRecord_inj` at `T := OutSummary`.
   - Membership follows by S1a's targets 1–4 and the audit's note-6 bridge
     (canonical decoding, outside-window rejection by `recordStepTM`'s false
     verdict, path lifting from the true initial configuration, all accepting
     vertices tested, the initial vertex in the table).
7. **Time:**
   - `counterLoop_time_le`: `V·B + 4V + 2|w| + 2` with `B = O(V·L + n)`. Add the
     constructor and startup.
   - Everything is at most `K·2^{c'(S n+1)}`, by the generalized `configBound`
     arithmetic and `n + 2 ≤ 2^{S n + 1}`.
   - All budgets are evaluated at `n` itself. **No monotonicity of `S` is used.**

#### Decisions for the user (12.8.x)

1. **Binary records** (recommended). The rows stay on the `Bool` counter stack,
   with no generic increment or `counterLoopTM`. The alternative is a
   rich-alphabet record: one cell per simulated cell, a simpler step machine, and
   `alphabet_reduction{,_spaceUsed}` at the end. It needs `incrementTM`,
   `decrementTM` and `counterLoopTM` generalized over two designated digit
   symbols (Catalog is G1-owned; CounterLoop is not).
2. **`Cfg.InWindow` relocation** from TQBF to `Build/CfgRecord.lean`, after C1d.
3. **`recordStepTM`'s contract form:** first-return with a bound (recommended),
   or an exact closed form.
4. **`PATH` hardness engine:** ARM (as sketched) or TM record rows with space
   clauses.
5. **Fold and seek in Catalog** (one trace family, after G1), or in `Scan` now
   with their own private skeleton. The latter is faster, but it is a second
   trace of the R3 forward pass.
6. **EmitIterBody dedup** onto `inputCopyTM` in 12.2c T2 (coordinate with
   Aparna).

#### Decisions 12.8.1–12.8.6 (2026-10-10)

1. **Rich-alphabet records** (user): multi-track record cells, mark moves as
   G2 mapped sweeps, and Bool counter rows on rich tapes through **one new
   embedding transport**. Finished by `alphabet_reduction` and
   `alphabet_reduction_spaceUsed`. The maintainer's alternative below is
   adopted, and the binary plan above is superseded where they differ.
2. **`Cfg.InWindow` moves** verbatim to `Build/CfgRecord.lean` after C1d
   (default).
3. **`recordStepTM` has a first-return contract with a bound** (default).
4. **`PATH`-hardness stays on the ARM engine**, as audited (default). The
   record-row route remains an option.
5. **Fold and seek live in Catalog, after the G1 gate** (user), sharing the
   R3/G2 trace, one trace per routine family.
6. **EmitIterBody's private input-copy startup is re-derived** from the new
   input rows in 12.2c T2, with the ch7 owner (default).

**Next.** A revised statement draft for the rich design. What can start
now: the embedding transport and the alphabet-generic input and
constant-write rows. The record rows, fold and seek wait for G1 and G2.

#### Maintainer's alternative for 12.8.1: rich-alphabet records through one embedding transport

Records could follow the §13d pattern instead of being bit-coded. Each record
cell is one rich symbol with tracks (content `Option Bool`, head mark, field
separators), as in the G3 `ZoneCell` carrier. Moving a head mark is then a G2
mapped sweep on one track, and no per-tape `markShiftTM` is needed. Fields
compare through the generic framed compare, and folds read one symbol per
cell.

The binary rows (`incrementTM`, `decrementTM`, `counterLoopTM`, the compare
contracts) need not be generalized. **One new transport lemma** runs them on
rich tapes: the embedding analogue of §12.7's `mapWorkSymbols`, which lifts a
`Bool` machine along `e : Bool ↪ Γ`. Its contract holds from configurations
whose work cells all lie in the image of `e` or are blank, which a dedicated
counter tape satisfies.

The simulator is finished by `alphabet_reduction` for time and by
`alphabet_reduction_spaceUsed` for space (space at most `(N+1)·space + k`).
The latter keeps Savitch and the space hierarchy within their bounds. The
input-position field stays binary over designated digits, so record length
stays `O(k·s + log n + |Q|)`.

The cost is the transport lemma, and records that wait for G2's mapped sweeps
(after the G1 gate). The gain is that the record machines become compositions
of generic rows instead of bit-group machines, and §12.8 and §13d share one
multi-track discipline.


### 12.8a Statement draft for the rich-alphabet design (2026-10-10)

*Recorded from the S1 agent's draft. Its probe is `campaign/items/s12-8/S128StatementsProbe.lean.txt`; run by the maintainer against the G1 side-branch tree it gives 0 errors and 12 sorry warnings, one per statement left to the fill. Maintainer decisions O1, O4, O5, O6 and the user's O2, O3, O7 are recorded at the end (§8).*

*Landed as statements on 2026-10-11, branch `integrate/s12-8-statements`: §8 lists the landed names, which supersede the draft's below where they differ, the changes from the draft, the R8.0b target signatures, and the open questions for the statement gate.*

*Draft for the statement phase, 2026-10-10. Base: campaign `19964447`; G1 side branch `s13d/g1`
(`10c2c08d`, PR #15, awaiting its gate).*

**Probe.** `drafts/s12-8-probe.lean`, with its output in `s12-8-probe.out`. It contains the
exact Lean of everything below.

- Against the G1 tree (`tools/leanprobe-g1.sh`): **0 errors, 0 warnings other than 12
  `declaration uses 'sorry'`**, one per proposed statement whose proof is fill work.
- Part A, the transport, is fully proved and also elaborates at the campaign HEAD
  (`tools/leanprobe.sh`, extracted as `s1work/p8/partA-head.lean`): 0 errors, 0 warnings.
- Every exact time below that the probe could execute was checked by `decide` on concrete
  configurations (§12.6 practice). That covers seek, the constant writer, the scan with a
  mark-shift instance, the input copier, and the framed compare at displaced heads.

#### 0. What the rich design needs, and the one gap in the decision as worded

Decision 12.8.1 adopts rich record cells, with the `Bool` counter rows run on rich tapes
through one embedding transport. The transport (R8.0) does what was asked:

- it lifts **any** `Bool` machine along `e : Bool ↪ Γ`;
- the lifted increment and decrement rows run on a dedicated digit tape inside a rich host,
  through G1's generic R1 (Part B of the probe).

**It cannot lift a loop with a rich body.** `counterLoopTM M` requires
`M : MultiTapeTM k Bool S`, so lifting it only serves `Bool` bodies. S1b's BFS round, Savitch's
frame step and every record row have rich bodies. After G1, no loop host exists over a
non-`Bool` alphabet. Decision 13d.7 generalized only Seam, Embed, `bufferTape` and the R3
sweeps. It deferred the loop hosts "only when a large-alphabet consumer needs them", and
§12.8's records are that consumer.

The rich design therefore needs **R8.0b, `counterLoopTMVia`**, a counter loop over any
alphabet:

- the body runs through R1 on the first `k` tapes;
- the counter is a dedicated last tape of digits `e b`, decremented by the lifted
  `decrementTM 1 0`, also through R1.

No new trace is needed. The existing round induction is generalized in place, and the
`Bool` contracts are re-derived from the generic ones: at `e = Function.Embedding.refl Bool`
the two tables agree, so Z5's `MultiTapeTM.runFrom_eq_of_agreeOn` transfers. This is the one
substantive addition to the decision; see §5 for its sequencing.

Two smaller findings:

- **The tag type.** `alphabet_reduction` needs `[Fintype Γ]`, and
  `Γ = RecSym N.State T` is `Fintype` only when `T` is. `Turing.OutSummary`, which is frozen,
  derives only `DecidableEq`. So S1b uses `T := Fin 3` through a code of the summary, as S1a's
  private counting already does, or sanctions a `Fintype OutSummary` export. Open decision O4.
- **Space on foreign inputs.** `alphabet_reduction_spaceUsed` hypothesizes
  `∀ x : List Γ, ∀ t, spaceUsed ≤ S |x|`, that is, over **all** rich inputs, including
  non-`Bool` ones. A lifted `Bool` machine reads a foreign symbol as a blank (`decodeBool`), so
  its space on such inputs is not controlled. Every rich space-bounded simulator (Savitch, the
  space hierarchy) must therefore start with a native **input validation fold**, R8.5d, and stop
  on a foreign symbol.

#### 1. R8.0 — the embedding transport

**Home: a new low file `TuringMachine/SymbolLift.lean`, importing `TuringMachine/Finite`.**
The alternative was CounterLoop's `SymbolTransport` section. The transport uses only
`Configuration`/`Deterministic`/`Finite`, and it has consumers below `Build/`: the G3 carrier
(`ZoneSym := Bool ⊕ …` with `e := Sum.inl`) and the Robustness layer. A low home also keeps it
out of `CounterLoop.lean` while that file's §12.7 fill gate is open.

- **Imports:** `Finite` imports `Deterministic`, which imports `Configuration`. Its up-closure
  contains no `Build/` module, so no cycle is possible.
- **Facade:** the `TuringMachine` facade gains one import.
- `mapWorkSymbols` (CounterLoop) can join it at 12.2c's per-theme split.

**Exact declarations** (verbatim in probe Part A, proved):

```lean
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) : decodeBool e (e b) = some b
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State   -- writes/emission mapped by e
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) : Cfg k Γ State (x.map e)
  -- state, heads unchanged; inputPos := Fin.cast _ c.inputPos; cells and output mapped by e
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State   -- reads through decodeBool e, writes through e
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M) (e) {x} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e
lemma MultiTapeTM.liftSymbols_initCfg : (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e
lemma MultiTapeTM.liftSymbols_spaceUsed : (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t
@[simp] lemma Cfg.liftSymbols_state, Cfg.liftSymbols_workTapePos   -- rfl
lemma Cfg.liftSymbols_inputSymbol : (c.liftSymbols e).inputSymbol = c.inputSymbol.map e
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ
theorem FinTM.liftSymbols_computesFunInTimeVia (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T
```

The one-step lemma `MultiTapeTM.liftSymbols_step`, and `moveInputPos_cast`, are `private` in
the real file.

**Proof notes.**

- `MultiTapeTM.runFrom_comm_of_step` (vendored `Deterministic.lean`) is single-alphabet, so the
  run lemma is a direct induction with `runFrom_succ_eq_step`.
- The one-step lemma decodes the input symbol through
  `Cfg.liftSymbols_inputSymbol`, which needs `Fin.cast` care on the boundary tests.
- The work reads decode by `decodeBool_apply`. Writes commute with `Function.update`.
- The output is `(Option.map e o).toList = o.toList.map e`.

**Corollaries after the G1 merge** (probe Part B, proved). These touch no G1 file:

- `FinTM.bufferTape_map (e) (w) (p) : bufferTape (w.map e) p = (bufferTape w p).map e`. It lives
  in `SymbolLift.lean`, which then imports `Simulation`.
- **Framed lifted rows are one-line consequences.** The probe proves the increment success case:
  `((incrementTM k i).liftSymbols e).runFrom (d.liftSymbols e) (2p+2) = (finish).liftSymbols e`.
  So no per-row lifted statement is proposed; consumers rewrite with
  `liftSymbols_runFrom` and cite the `Bool` row.
- **Dedicated digit tape inside a rich host:**
  `(embedEmitTM ι ((incrementTM 1 0).liftSymbols e)).runFrom (embedEmitCfg ι tapes heads pre
  (d.liftSymbols e)) t = embedEmitCfg ι tapes heads pre ((… .runFrom d t).liftSymbols e)`. The
  host's other tapes (rich records) are R1's frame, so the transport's in-range hypothesis is
  only about the dedicated tape. This is the "dedicated counter tape" discipline of decision
  12.8.1, in usable form.

**Finishing.** Two cases:

- **Time.** A rich decider `D : FinTM Γ` with
  `D.ComputesFunInTimeVia e (fun x => [indicator L x]) T` becomes `FinTM Bool` by
  `FinTM.alphabet_reduction e D f T`, which gives `∃ c M', M'.ComputesFunInTime f (c·(T+1))`.
  The constructor and every `Bool` subroutine enter `D` as `FinTM.liftSymbols` /
  `MultiTapeTM.liftSymbols`, with unchanged time (`liftSymbols_computesFunInTimeVia`) and space
  (`liftSymbols_spaceUsed`).
- **Space.** Use `alphabet_reduction_spaceUsed`, subject to the foreign-input caveat of §0.

##### R8.0b — `counterLoopTMVia`, the counter loop over any alphabet

**Home:** `Build/CounterLoop.lean`. **When:** after the G1 gate (it needs generic
`embedEmitTM`/`embedEmitCfg`) **and** after the §12.7 fill gate. The probe's Part E has the
exact text.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1)
def counterLoopTMVia {k} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : (embedEmitTM Fin.castSuccEmb M) redirected by counterLoopRedirect a exit
  -- .dec f  : (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)) redirected by counterLoopDecExit a
  -- .done / .escape stationary
theorem counterLoopTMVia_run_done   -- counterLoopTM_run_done verbatim with Bool ↦ Γ, plus:
    (hw : ∀ p, -1 ≤ p → p ≤ |w| → ct (cp + p) = bufferTape (w.map e) p)   -- w : List Bool
    -- finish counter cells: `some (e true)`; time `Σ τ + counterOverhead w (d+1)` (unchanged)
theorem counterLoopTMVia_run_escape -- counterLoopTM_run_escape likewise; counter
    -- `bufferTape ((counterWord w (r₀+1)).map e)`
```

- **In-place generalizations (types only, bodies verbatim, G1 rule 2):** `counterLoopCfg` and
  `counterLoopOrbit` become `{Symbol : Type}`. The probe states them as `…Via` copies only to
  avoid a clash.
- `counterLoopTM`, its definition and all `Bool` statements stay byte-identical. Their **proof
  bodies** are swapped to instantiate the generic contracts. The route is
  `runFrom_eq_of_agreeOn` between `counterLoopTM M a exit` and
  `counterLoopTMVia (Function.Embedding.refl Bool) M a exit`. Their dec-phase tables agree
  pointwise (`decodeBool refl γ = some γ`, `Option.map refl = id`, and R1's single-tape action
  equals `decrementTM (k+1) (Fin.last k)`'s), and the other phases agree definitionally.
- **One round induction; net private count down.** `counterLoop_time_le` and the counter
  arithmetic are alphabet-free and reused as they are.

#### 2. The record carrier — `Build/CfgRecord.lean`

**Imports:** `Build/CounterLoop` (for R8.0b) and `TuringMachine/SymbolLift`. **No
`SpaceComplexity` import:** injectivity is stated componentwise rather than through
`ConfigCount.core`, and ConfigGraph converts. **When:** after the G1 merge, since `fieldsTape`
uses generic `bufferTape`. The window predicate lands with the 12.8.2 relocation (after C1d).
The probe's Part F has the exact text.

```lean
inductive RecSym (Q T : Type) where
  | digit (b : Bool)                          -- the `e` of the lift: input, position field, counters
  | cell (content : Option Bool) (mark : Bool)-- one simulated work cell: content track + head-mark track
  | st (q : Option Q)                         -- the state cell
  | tag (τ : T)                               -- the tag cell (emission summary)
deriving DecidableEq
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) := derive_fintype% _
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit       -- little-endian, fixed width
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length                      -- 2 ^ posWidth n > n + 1
def cfgRecord {k Q T} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) : List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::                                                     -- F0
  ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::       -- F1, binary over digits
  (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>     -- F2 … F(k+1)
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
  [[RecSym.tag τ]])                                                          -- F(k+2)
def joinFields (fs : List (List Γ)) : List (Option Γ) := List.intercalate [none] (fs.map (List.map some))
def fieldsTape (fs : List (List Γ)) (z : ℤ) : Option Γ := if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none
def fieldOffset (fs : List (List Γ)) (j : ℕ) : ℕ := ((fs.take j).map (·.length + 1)).sum
theorem fieldsTape_field (fs) (j) (hj : j < fs.length) : ∀ p, -1 ≤ p → p ≤ |fs[j]| →
    fieldsTape fs (fieldOffset fs j + p) = FinTM.bufferTape fs[j] p   -- each field is a framed word
theorem cfgRecord_inj (s) (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ'
theorem cfgRecord_length : (cfgRecord s c τ).length = k + 3   -- proved in the probe
def RecordValid (k n s : ℕ) (Q T) (fs) : Prop :=
  ∃ x (c : Cfg k Bool Q x) τ, x.length = n ∧ c.InWindow s ∧ cfgRecord s c τ = fs
theorem recordValid_iff (n s fs) : RecordValid k n s Q T fs ↔ fs.length = k + 3 ∧ (∃ q, fs[0] = [.st q]) ∧
    (fs[1] is posWidth n digits of value ≤ n + 1) ∧ (each tape field: 2s+1 `.cell`s, exactly one mark) ∧
    (∃ τ, fs[k+2] = [.tag τ])            -- the scan-checkable form, for `recordValidTM`
def RecordAt (d : Cfg K Γ S x) (r : Fin K) (fs) : Prop :=
  ∀ p, -1 ≤ p → p ≤ |joinFields fs| → d.workTapes r (d.workTapePos r + p) = fieldsTape fs p
```

- **Layout discipline.** One blank between fields and between records; no field is empty (F0
  and the tag have one cell, F1 has `posWidth n ≥ 1` cells, each tape field `2s+1` cells). So
  two consecutive blanks mark the end of a table, and every field is a §12.6-delimited word.
  This is the G3 separator discipline, so the generic framed rows apply field by field with no
  save/restore.
- **Space.** A record has `k(2s+1) + posWidth n + 2` cells plus `k + 2` separators, which is
  `O(k·s + log n + 1)`. That is `O(S n)` at `s = c₀·S n` with `S ≥ logSpace`. With
  `alphabet_reduction_spaceUsed`'s `c·(space+1)`, Savitch stays in `SPACE(S²)`.
- **Window predicate.** The probe uses `WindowedP`, a verbatim copy of TQBF's
  `Turing.Cfg.InWindow`. The real file uses `Cfg.InWindow`, relocated here (12.8.2). It **must
  land in the same change** that deletes TQBF's copy: once ConfigGraph imports `CfgRecord` (at
  S1b), TQBF, which is downstream, would otherwise see two definitions.

#### 3. The rows, restated for the rich design

Template (from the §12.8 note), with one change of form:

- **Machines that are single sweeps are defined** and get the §12.6 framed contract: exact
  time, finish configuration, no earlier exit, trajectory.
- **Composite modules are existential**, in the `exists_installCallTM` style
  (`∃ R entry exit C, …`): a first-return time `t ≤ C·(size)`, no earlier exit, an exact finish
  configuration, and the scratch tapes and heads restored.

The constants are indicative; the statement phase fixes them by execution. Tags: **[now]**
can land on the campaign branch before G1 merges. **[G1-merge]** touches no G1 file but uses
G1's generic statements. **[Catalog/G1]** goes in a G1-owned file, after the G1 gate. **[G2]**
is proposed as a G2 statement. **[rec]** is a record row, filled after G2 and the
Catalog/G1 rows.

| Row | Tag | Statement (probe part) | Contract |
|---|---|---|---|
| **R8.0** transport | **[now]** | `MultiTapeTM.liftSymbols_runFrom` and the rest of §1 (A) | proved |
| R8.0 corollaries | [G1-merge] | `FinTM.bufferTape_map`; the R1 composition (B) | proved |
| **R8.0b** `counterLoopTMVia` | [Catalog/G1]+§12.7 gate (CounterLoop) | `counterLoopTMVia_run_done/_escape` (E) | exact, as §12.7 |
| **R8.1** framed compare | [Catalog/G1] | `compareTM_run_ofCfg {Symbol} [DecidableEq Symbol]` (D) | `∃ δ ≤ min |u| |v|`, exact time `2δ+2`, finish `{d with state := done (decide (u = v))}`, no earlier verdict, trajectory `[pos−1, pos+δ]`. Canonical `compareTM_run` re-derived (body swap); the trace generalizes `catalog_compare_trace` |
| **R8.2** `scanTM δf δb a₀` (two-pass transducer) | **[G2]** | `scanTM_run_ofCfg` (D) | exact `2|w|+2`; interval rewritten to `(scanResult δf δb a₀ w).2`, verdict `done (scanResult …).1`; trajectory `[pos−1, pos+|w|]` |
| **R8.3** `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` | [Catalog/G1] | `skipTM_run_ofCfg` (D); landed with `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | skip: exact `|w|+1`, head to `pos+|w|+1`. Landed: skip back is skip's inverse, exact `|u|+3` from the next field's first cell to `u`'s; seek end exact `D+1` to `pos+D`, `D = fieldOffset ws |ws|`, `ws ≠ []`; seek start exact `D+4` back to the table start. Nothing written; the seeks stop at two consecutive blanks (table ends) |
| **R8.4** `writeConstTM i w₀` | [G1-merge] (Scan) | `writeConstTM_run_ofCfg` (C) | exact `2|w₀|+2` (executed), old contents arbitrary, head returns |
| R8.4′ `writeAdvTM i w₀` | [G1-merge] (Scan) | landed: `writeAdvTM_run_ofCfg` | writes `w₀` and leaves the head at `pos + |w₀|`, exact `|w₀| + 1`; the advancing round of `expandTM`. Landed cyclic, over `Fin (|w₀|+1)`: it returns to its start state `0`, the counter-loop round shape |
| **R8.5a** `inputCopyTM i` | [G1-merge] (Scan) | `inputCopyTM_run_ofCfg` (C) | from input position 1, exact `2|x|+2` (executed); both heads return in lockstep (no left delimiter needed) |
| **R8.5b** `exists_inputSeekTM` (`Bool`) | **[now]** | (C) | `∃ R … C`; moves the input head to the binary value on a dedicated tape, `t ≤ C·(|w| + pos + p + 1)`; tapes restored |
| **R8.5c** `exists_inputLengthTM` (`Bool`) | statement now; fill after R8.3 (it needs `skipTM` for the width extension) | — | writes `Nat.bits |x|` on a dedicated tape: per input symbol, `incrementTM` with width extension on overflow (`seekEnd` + `writeConst`), `t ≤ C·(|x|+1)` amortized (§12.7 potential) |
| **R8.5d** `inputFoldTM δ a₀` | [G1-merge] (Scan) | — | native scan of the input with a finite fold, verdict `done (x.foldl δ a₀)`, exact `2|x|+2`; the foreign-symbol validator of §0 |
| **R8.5e** `exists_inputCallTM` | [G1-merge] (`Build/InputCall.lean`; needs R8.5a) | — | `inputCopyTM` (at `Bool`, or lifted) + `exists_installCallTM`: a function-level machine on the native input at a clean seam |
| **R8.6** `exists_expandTM pat` (`Bool`); landed as the definition `expandTM` | [G1-merge] (CounterLoop; needs R8.4′) | landed: `expandTM_run_ofCfg` | `counterLoopTM` round = `writeAdvTM pat`; writes `pat` `d` times contiguously; exact `d(|pat|+1) + counterOverhead w (d+1)` |
| **R8.7** record rows | **[rec]** | `exists_recordStepTM`, `exists_recordEqTM` (G); landed with `exists_recordTestTM`; the rest below | first-return form; landed with `yes ≠ no` in each existential |
| **R8.8** `seamCompTM_runFrom_left` (promotion) + `seamCompTM₂_run_ofCfg` | [Catalog/G1] (Seam) | §12.8 note | statement unchanged from the private `seamComp_left` |

**R8.2 replaces fold, map, mark shift and odometer: one row, one trace.** It is proposed **as a
G2 statement**. Its instances:

- **fold:** `δf a γ := (δ a γ, γ)`, `δb` the identity;
- **in-place map** `f`: `δf a γ := (a, f γ)`;
- **head-mark shift right:** `δf prev γ := (mark γ, setMark γ prev)`, the forward delay (the probe
  checks a concrete shift);
- **shift left:** the same delay on the backward pass;
- **record odometer:** a carry transducer;
- **validity checks:** folds.

G2's planned two-tape `copyMapTM`/`transferMapTM` (§13d) are not needed by §12.8: records move
by plain generic `copyTM`. If G2 keeps them, one request: let `merge` take `Option Γ`, so that
blank destinations (scratch) are admitted. **Decision 12.8.5 is honored:** fold, and with it map,
is a Catalog row sharing the R3/G2 trace (`catalog_trace_run`), since G2 lives in Catalog.

**R8.7, the record rows.**

- All are existential modules over `RecSym Q T`.
- **Entry conditions:** the record at tape `0` (`RecordAt`), the scratch tapes `j ≠ 0` blank,
  and the native input `x.map RecSym.digitEmb`.
- **Exit conditions:** heads, input position, scratch and output restored.
- They are built from R8.0/R8.0b, R8.1–R8.5 and R2 seams, with **no private re-trace**.

| Module | Verdict / effect | Composition |
|---|---|---|
| `exists_recordStepTM M upd (hupd : ∀ τ, upd τ none = τ)` (GAP-4, exact text in G) | `yes` and record of `M.step c` with tag `upd τ (M.outputSymbol c)` if `(M.step c).InWindow s`; else `no`, nothing changed; `t ≤ C·(L + |x| + 1)` | read: `scanTM` folds on F0, the tag and the tape fields (scanned symbols and edge flags) via `skipTM`; copy F1 to a dedicated digit tape (`copyTM`), run the lifted `inputSeekTM`, read the input symbol, restore; finite dispatch on `M.tr`; apply: `scanTM` maps (content at the mark, F0, tag) and delay shifts (marks), F1 `±1` by the lifted increment/decrement on the dedicated tape with copy back, clamp from the edge data |
| `exists_recordEqTM` (G) | `yes` iff the two field lists are equal | `k+3` framed compares (R8.1) with `skipTM`s |
| `exists_recordTestTM P` | `P (state, tag)` | two `scanTM` folds |
| `exists_recordValidTM` | `RecordValid` via `recordValid_iff` | `scanTM` folds per field |
| `exists_recordInitTM` | writes `cfgRecord s (initCfg x) τ₀` from `bits (S n)`-style radius digits | `exists_inputLengthTM` (lifted), `exists_expandTM` (lifted) for the window halves, `scanTM` maps, `writeConstTM` |
| `exists_recordNextTM` | next valid record in odometer order, or overflow | `scanTM` carry over all fields + `exists_recordValidTM` filter, under `counterLoopTMVia` |
| `exists_tableAppendTM`, `exists_tableFindTM P` | append at `seekEndTM`; first record satisfying a fold, with an escape if none | `copyTM`, `seekEndTM`, `scanTM`, `counterLoopTMVia` |

#### 4. S1b's machine plan, recomposed (rich)

*Historical (2026-10-14): S1b stopped (fills-6), and its target is proved at ARM level (§14 H12).
The rows this plan uses keep one remaining consumer, B6's window route (rows 17–18).*

**Parameters.** `Γ := RecSym N.State (Fin 3)`, with the tag being the output summary through
its `Fin 3` code (O4), and `e := RecSym.digitEmb`. The host is a `FinTM Γ`.

**Tapes:**

- `Tab`, the table;
- `Cur₀` and `Cur₁`, the successor workspaces;
- scratch for the record modules;
- dedicated digit tapes: `Rad` (radius), `Len`, `Cnt` (the outer counter, last tape) and
  `Cnt'` (inner loops);
- the lifted constructor's bank and capture tape.

1. **Validate** with `inputFoldTM`. On a foreign symbol, emit `e false` and halt. This is needed
   only for space, but it is cheap.
2. **Radius.** Run `M_S.liftSymbols e` under generic `embedSilentRetTM` with its output
   captured on `Rad`, then rewind. Time at most `M_S.configBound n (a·S n)`
   (`of_spaceUsed_le` plus `liftSymbols_runFrom`).
3. **Window template.**
   - Lifted `exists_expandTM` with counter `bits (S n)` and pattern `false^{c₀}` writes the left
     half.
   - `writeConstTM [.cell none true]` writes the center.
   - `expandTM` again writes the right half.
   - A `scanTM` map turns the digits into `.cell none false`.

   No multiplication by `c₀` is needed: the pattern length carries it.
4. **Initial record.** `exists_recordInitTM` writes it, plus a one-digit flag field `[digit
   false]` ("unprocessed").
5. **Outer counter.** Copy the template fields `c_N` times onto `Cnt` (`copyTM` + `skipTM`),
   then map every cell to `digit true` (`scanTM`). Its value `2^{c_N·W} − 1` exceeds the record
   count `V` with `c_N := ⌈log₂(3(|Q|+1))⌉ + 4`. Here `W` is the record's cell count, and the
   proof uses `2^{posWidth n} ≥ n+2` and `8^{2s+1} ≥ 3^{2s+1}(2s+1)`.
6. **BFS** with `counterLoopTMVia e Round a (some ex)`. A round:
   - `exists_tableFindTM` finds the first record with flag `false` (escaping to `ex` if none),
     and copies it to `Cur₀` and `Cur₁`;
   - `exists_recordStepTM (N.fixChoice false)` runs on `Cur₀`, and
     `exists_recordStepTM (N.fixChoice true)` on `Cur₁`. The upd is the summary's append table
     on the code;
   - for each `yes`, an inner `counterLoopTMVia` over the table with `exists_recordEqTM`
     decides membership, and `exists_tableAppendTM` appends a new record with flag `false`;
   - the processed record's flag is set (`scanTM` map), the workspaces are cleared
     (`clearTM`), and the table head is rewound (`seekStartTM`).

   Both exits are wired by R8.8.
7. **Verdict.** `exists_tableFindTM (accept)` scans for a record with state `none` and tag
   `accept`. Emit `e true` or `e false`, then halt.
8. **Finish.** `alphabet_reduction` gives a `FinTM Bool` within `c·(T + 1)`.
9. **Correctness** is §12.8's chain, with `cfgRecord_inj` in place of the bit codec:
   - `T := Fin 3` identifies records with `coreSum`s;
   - note-6's bridge applies, the outside-window rejection being `recordStepTM`'s `no`;
   - S1a's four lemmas finish.
10. **Time.**
    - `counterLoop_time_le` gives `V·B + 4V + 2|w| + 2`, with `B = O(V·(L+F) + n)` from the
      nested table loop.
    - Add the startup terms: the constructor bound, `O(S n)`-cost expansions, and
      `O(n log n)` input length.
    - Then `alphabet_reduction`'s `c(T+1)`. The result is at most `K·2^{c'(S n+1)}`.
    - Every budget is evaluated at `n`; no monotonicity of `S` is used.

#### 5. Sequencing — what can be issued before the G1 gate closes

| Item | Lands | Blocked on |
|---|---|---|
| **R8.0 transport** (`SymbolLift.lean`) | **now**. The probe's Part A *is* the proof; a maintainer pre-issue landing or a tiny batch | nothing |
| **R8.5b** `exists_inputSeekTM` (`Bool`; composed of `copyTM`, `timed_rewind`, `counterLoopTM`, `clearTM`, all public at HEAD) | **now**, as a statement phase plus a fill batch | nothing; it lifts to rich hosts by R8.0 |
| R8.5c, R8.5e, R8.6 (`Bool` rows needing Scan or seek) | statements now; fills after the G1 merge (R8.5e, R8.6) or after R8.3 (R8.5c) | G1 merge / R8.3 |
| Statements of **everything else** | **draft now** (this document, probe green on `s13d/g1`) | — |
| R8.0 corollaries, R8.4, R8.5a/d, the `CfgRecord` pure layer | after **G1 merges** (no G1 file edited) | G1 gate; CfgRecord's `InWindow` also on C1d |
| R8.1, R8.3, R8.8 | after the **G1 gate**, in Catalog/Seam | G1 gate; coordinate with G2/G4 (one trace) |
| R8.2 `scanTM` | with **G2** | G1 gate; G2's statement phase adopts it |
| **R8.0b** `counterLoopTMVia` | after the **G1 gate and the §12.7 fill gate** | both gates |
| R8.7 record rows | after the R8.2 fill (G2) and the R8.1/R8.3 fills | G2 fill |
| S1b | after R8.7 | — |

**The sequencing change versus the note:** R8.0b is new, and it sits on two gates (G1, §12.7).
It is the long pole for every rich consumer, since no rich loop exists without it. Some things
can be issued before the G1 gate closes:

- R8.0, which the probe proves;
- R8.5b;
- the statement phase of every other row (the probe is green on `s13d/g1`).

The critical path is then the G1 gate, then R8.0b with R8.2 (G2) and R8.1/R8.3, then R8.7,
then S1b. Two items that the note called "landable now" in fact need the G1 merge, because
their statements use the generic `bufferTape`: `writeConstTM` and the input rows. `expandTM`
needs the advancing writer R8.4′.

#### 6. Per-consumer rows (updated)

| Consumer | Rows |
|---|---|
| **S1b** | §4: R8.0, R8.0b, R8.1–R8.5, R8.6, R8.7 (step, eq, test, init, table rows), R8.8, `alphabet_reduction` |
| **Savitch** | Rich records with binary F1 (`O(S)` cells); frame stack on a rich tape; R8.7 `recordStepTM` (both choice bits) + `recordEqTM` for adjacency; `recordNextTM` + `recordValidTM` for midpoints; R8.3 over frames; `copyTM`/`clearTM` at fixed intervals (note 7); R8.0b loops; R8.8; R8.5d validation; `alphabet_reduction_spaceUsed` |
| `spaceConstructible_*` | `Bool` only: R8.5c, R8.6, `incrementTM` |
| `PATH_NLComplete` (hardness) | ARM engine (12.8.4); no §12.8 row |
| `PATH_mem_NL` | R8.5b, once the nondeterministic host exists (SC-3; superseded 2026-10-13: C2 is written as programs, §16b item 4) |
| Space hierarchy | **Superseded 2026-10-12 by the window route** (§16b item 3; the RD-3 statement gate, minor 2): R8.7's initial-record, test and step rows under a configuration-count clock (`counterLoopTMVia`), through H2, H3 and H5, with R8.5d for input validation. The earlier route (R8.0b's budget loop, R8.8's success/cap exits, R8.1's budget comparison, `clearTM` resets, and no R8.7) is dropped |
| `TQBF_mem_PSPACE` | R8.2 (validation folds, clause evaluation, the trit odometer), R8.5b (input re-reads), R8.3 |
| `NP_subset_PSPACE` | `incrementTM`, `vhostEmitTM`, R8.8 |
| **G3/G4 (§13d)** | R8.3 (zone scanning across separators), R8.2 (per-track maps), R8.0 (Bool counters on `ZoneSym` tapes via `e := Sum.inl`) |

#### 7. Open decisions

- **O1, transport home.** New `TuringMachine/SymbolLift.lean` (recommended), or CounterLoop's
  `SymbolTransport` section (during its open gate).
- **O2, R8.0b route.** In-place proof generalization with the `Bool` contracts re-derived by Z5
  (recommended; one round induction). The alternative is a second host with its own induction,
  which is a duplicated trace.
- **O3, `scanTM` as a G2 statement.** It needs G2's agreement. Separately, the optional
  `merge : Option Γ → Δ → Γ` request for `copyMapTM`.
- **O4, the S1b tag type.** `Fin 3` code (recommended; no frozen-surface change), or a sanctioned
  `Fintype OutSummary` export in ConfigGraph.
- **O5, table seeks.** `seekEndTM` and `seekStartTM` (double-blank stops) in the skip family, or
  as `counterLoopTMVia` loops over `skipTM` (slower, no new row).
- **O6, input validation (R8.5d).** Mandatory for rich space-bounded consumers. Confirm, or
  require every rich row's space bound to be input-independent instead (harder to state).
- **O7, R8.0 now.** Whether the transport lands as a maintainer pre-issue lemma, since the
  probe proof is complete (one file, about 120 lines), or through a statement gate plus fill
  like the other §12 rows.

#### 8. Decisions and the landed statement layer (2026-10-11)

**Decisions.**

- **User:** O2, generalize `counterLoopTM` in place, with the `Bool` contracts
  re-derived by Z5 (R8.0b, a later batch; target signatures below); O3, G2 is
  `scanTM`; O7, the transport lands by PR plus the §12.8 statement gate.
- **Maintainer:** O1, `TuringMachine/SymbolLift.lean` (landed, PR #16); O4, the
  `Fin 3` tag code; O5, dedicated `seekEndTM`/`seekStartTM` rows; O6, input
  validation (R8.5d) is mandatory for rich space-bounded consumers.

**Landed** on `integrate/s12-8-statements` (campaign `5e438f50` with PR #16,
merged at `b28e22ea`). Every machine and carrier is a real definition. Every
contract is sorried with a proof sketch, except the two results already
proved, which keep their proofs: `seamCompTM_runFrom_left`, promoted verbatim,
and `cfgRecord_length`. There are 25 new sorries. Records:
`campaign/gates/s12-8-statements/logs/` and
`campaign/items/s12-8/S128StatementsPreship.lean.txt`.

| Row | File | Landed declarations | Contract |
|---|---|---|---|
| one-tape actions | `Build/Catalog.lean`, Part 3 | `tapeAction`, `inputMoveAction` | the transition-table vocabulary of every §12.8 machine |
| field layout | Catalog, Part 3 | `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field` | each field is a §12.6 delimited word in place |
| R8.1 | Catalog, Part 3 | `compareTM_run_ofCfg` | as drafted |
| R8.3 | Catalog, Part 3 | `SeekPhase`; `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM`, each with `_run_ofCfg` | as in the §3 row, with trajectories |
| R8.2, the G2 core | Catalog, Part 3 | `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanTM_run_ofCfg`; the steps `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`; the identities `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`, `scanResult_carry` | the scan contract as drafted. The instances are pure identities of `scanResult`, so the scan keeps one framed contract |
| R8.4, R8.4′, R8.5a, R8.5d | new `Build/Scan.lean` | `WritePhase`, `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`, each with `_run_ofCfg` | constant writer `2|w₀|+2`; advancing writer `|w₀|+1`, cyclic; input copy and input fold `2|x|+2` from input position `1` |
| R8.5e, R8.5b | new `Build/InputCall.lean` | `FinTM.exists_inputCallTM`, `exists_inputSeekTM` | first-return modules |
| R8.6 | `Build/CounterLoop.lean` | `expandTM := counterLoopTM (writeAdvTM k i pat) 0 none`, `expandTM_run_ofCfg` | exact `d(|pat|+1) + counterOverhead w (d+1)`, with `d` copies of `pat` from `pos` |
| R8.7 | new `Build/CfgRecord.lean` | `Cfg.InWindow` (relocated verbatim from `ClassPSPACE/TQBF.lean`, which now imports it); `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length` (proved), `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`; `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` | first-return modules with distinct verdict anchors |
| R8.8 | `Build/Seam.lean` | `seamCompTM_runFrom_left` (promoted), `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | one continuation per exit, each run unboundedly after the dispatch step |

**Changes from the draft.** Each was executed in the pre-ship probe where
executable.

1. **`yes ≠ no`** is part of every record row's existential. Without it, a
   module with `yes = no` satisfies `exists_recordEqTM` vacuously, and no
   consumer could branch on the verdict.
2. **The field layout lives in Catalog**, not in CfgRecord, because the seek
   rows' contracts are stated over it. CfgRecord imports Catalog and
   `SymbolLift`, not CounterLoop, since R8.0b is not in this step. TQBF's
   import closure gains Catalog, `SymbolLift` and CfgRecord; there is no
   cycle.
3. **`writeAdvTM` is cyclic** over `Fin (|w₀|+1)`. It returns to its start state
   `0`, so it is a counter-loop round as it stands. A seam caller that runs it
   once uses `seamReleaseTM`.
4. **R8.6 is the concrete `expandTM`** with an exact contract, not an
   existential.
5. **The seek family.** Skip back is the inverse of skip (`|u|+3`, from the
   next field's first cell), not its mirror. The seeks' exact times are `D+1`
   and `D+4`, with `D = fieldOffset ws |ws|`. Every row carries the §12.6
   trajectory clause.
6. **No new copier phase type.** The input copier reuses `SweepPhase`, and the
   input fold reuses `ScanPhase`.
7. **The scan instances** are stated as identities of `scanResult` rather than
   as five machine contracts. `scanTM_run_ofCfg` turns each into the
   instance's run.
8. **`Cfg.InWindow`** replaces the probe's `WindowedP`.
9. **One-tape actions.** The §12.8 machines' tables are written with two
   named actions, `tapeAction` and `inputMoveAction`, instead of literal
   `Action` tuples. With literal tuples, the copy-text screen found 17 new
   cross-file pairs: the input copier and the input fold against the R3
   sweeps and the scan. With the helpers there are none. Twelve new same-file
   pairs remain: the four seek tables among themselves, and the two writers.
   These are distinct small machines sharing their phases, not copied
   proofs. The proved R3 tables are unchanged.
10. **Not landed**, being outside this step:
    - `FinTM.bufferTape_map` and the other R8.0 corollaries;
    - R8.5c, `exists_inputLengthTM`;
    - R8.0b;
    - the record rows `exists_recordValidTM`, `exists_recordInitTM`,
      `exists_recordNextTM`, `exists_tableAppendTM` and
      `exists_tableFindTM`. Their statements need S1b's table layout (a
      header, the radius digits, the odometer order) and a template tape
      holding the widths a validity machine compares against.
11. **`MultiTapeTM.liftSymbols_step` is public** in the landed
    `SymbolLift.lean` (PR #16), as the transport's one-step form; §1 above
    made it private. Only `moveInputPos_cast` is private.

**R8.0b target signatures.** These land in a later batch, after this
statement gate. Home `Build/CounterLoop.lean`, which then imports
`SymbolLift`.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) := ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
  -- .dec f  : ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
  --             (counterLoopDecExit a)
  -- .done, .escape : stationary
-- generalized in place (types only, bodies verbatim; existing call sites unchanged):
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol} (q : Option (CounterLoopState S))
    (c : Cfg k Symbol S x) (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol} … -- otherwise verbatim
-- the generic contracts are counterLoopTM_run_done / counterLoopTM_run_escape verbatim, with
--   M, τ, c over Γ; ct : ℤ → Option Γ; counterLoopTM M a exit ↦ counterLoopTMVia e M a exit;
--   hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p,
--     for the counter word w : List Bool;
--   done finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q;
--   escape finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
--     then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q;
--   all four clauses kept (finish, no earlier exit, counter head range, body heads).
theorem counterLoopTMVia_run_done …
theorem counterLoopTMVia_run_escape …
-- counterLoopTM and its two contracts: statements byte-identical; proofs re-derived at
-- e := Function.Embedding.refl Bool through MultiTapeTM.runFrom_eq_of_agreeOn (Z5), the
-- decrement tables agreeing pointwise (decodeBool refl γ = some γ, Option.map refl = id).
```

**Governance.** Catalog and Seam are G1-owned files, and `scanTM` is the G2
core of the §13d revision. Under the §13d rule this branch therefore lands by a
PR the user merges, with its own statement gate. Nothing is pushed by the
agent.

**Open questions for the statement gate.**

1. **Skip back.** Is the inverse convention right (from the next field's
   start, `|u|+3`), or should it be the mirror of skip (from a word's last
   cell, `|u|+1`)?
2. **The empty table.** `seekEndTM` requires `ws ≠ []`, since an empty table's
   end is its start. Should tables carry a header field, so that every seek
   precondition is uniform?
3. **The cyclic writer.** Is `writeAdvTM`'s anchor-equals-start shape
   acceptable, or should it have a stationary `done` with the loop adapting
   it?
4. **Tape layouts of the record rows.** `exists_recordStepTM` has
   `K + 1` existential tapes with the record on tape `0`; `exists_recordEqTM`
   has 2 tapes; `exists_recordTestTM` has 1. Hosts embed them by R1. Is the
   fixed layout acceptable, or should each row take a tape selection? The
   step row's fill will also import InputCall, for the input seek, which
   enlarges TQBF's import closure again.
5. **The deferred record rows.** Should validity, init, next and the table
   rows enter this gate, or S1b's statement phase, once the table layout is
   fixed?
6. **The facade.** Scan, InputCall and CfgRecord are not wired into the
   `TuringMachine` facade, following the precedent of `SymbolLift`,
   CounterLoop and Zone. Is facade wiring wanted at this gate?
7. **G2's agreement** to `scanTM` as its core, and whether the planned
   `copyMapTM`/`transferMapTM` are still wanted. §12.8 does not need them.

#### 9. Statement gate, round 1: decisions and repairs (2026-10-11)

Round 1 failed with 0 blockers, 1 major, 7 minors and 39 notes
(`campaign/gates/s12-8-statements/findings.md`).

**Decisions** (user, the auditor's recommendations, on the open questions
of §8):

1. Skip back stays the **inverse** of skip, at `|u| + 3`.
2. Shared tables get a **fixed nonempty header field**, so seek end always
   has a field to stop after. The table ends are two blank cells before the
   header and two after the last field. From seek end's stopping blank, a
   consumer reaches the table start by skipping back over the last field
   and then seeking start. The deferred table rows are stated with this
   layout.
3. `writeAdvTM` stays **cyclic**. One-shot callers use `seamReleaseTM`.
4. The record rows keep their **fixed local tape layouts**, and hosts embed
   them by R1.
5. The deferred record rows (validity, init, next, table append and find)
   get **their own statement gate** with S1b's concrete layout, before
   S1b's fill uses them. R8.0b and R8.5c are explicit prerequisites.
6. The new modules are **wired into the `TuringMachine` facade** at this
   gate: `SymbolLift`, `Build/CounterLoop`, `Build/Scan`, `Build/InputCall`
   and `Build/CfgRecord`. Nine older files of the topic are also absent
   from the facade; they are recorded as `backlog.md` FAC-1.
7. G2's core is `scanTM`, and `copyMapTM`/`transferMapTM` stay for G3/G4
   (§13d, G2).

**Repairs** (for round 2):

- **Major 1: work-space clauses.** The record rows and the input seek
  bounded time but not the cells they visit, so they were too weak for
  Savitch and logspace consumers. Each now bounds every work head, through
  its verdict or exit, to `C·(size + 1)` cells of its entry position. The
  size is the record's layout length for the step and test rows, `fs`'s
  layout length for the equality row, and `|w|` for the seek. So the space
  does not depend on how far the native input head travels, and repeated
  calls compose. The step row's sketch now names the obligations the auditor
  identified: save and restore the host's input position in binary, and
  clamp the position field at `0` and `|x| + 1`.
- **Minor 2.** The input seek's rewind: `timed_rewind` stops at position
  `1` within `pos + 2` steps, and one left move follows.
- **Minor 3.** The input call's first-return clause splits on whether the
  callee's entry equals its exit. If it does, `seamReleaseTM` supplies a
  fresh entry first.
- **Minors 4, 5 and 6.** `recordValid_iff`'s validator needs width
  templates. A record determines the configuration *core* together with the
  tag. `fieldOffset`'s end formula needs `fs ≠ []`.
- **Minors 7 and 8.** Corrected in the records: the declfreeze log
  miscounted the promotion's citations (3, not 4), and Catalog's ledger
  denominator is now 459.

### 12.8b Record tables, the deferred record rows and R8.5c (statements landed 2026-10-11; design W1 accepted by the user as drafted)

**Why.** §12.8a §8 item 10 deferred five record rows. Their statements need S1b's table layout,
the radius digits, the odometer order, and a template that the validity machine compares
against. §12.8a §9 decision 2 fixed the table convention:
- a nonempty header;
- two blank cells before it, and two after the last field;
- an end-to-start adapter.

Decision 5 sent the deferred rows to their own gate. This increment states that layout, the
five rows, R8.5c, and three small additions the rows and their consumers need.

**Homes.**

| Module | Imports | Contents |
|---|---|---|
| `Build/InputLength.lean` | `Build/CounterLoop` | R8.5c, `exists_inputLengthTM`, alone |
| `Build/RecordTable.lean` | `Build/CfgRecord`, `Build/Seam`, `Build/InputLength` | the layout lemmas, the record template, tables, the adapter, field copy, find and append, and the template, init, validity and next rows |

- R8.5c gets its own small module so that the constructibility files can use it without the
  record layer. 12.2c may fold it into `InputCall`.
- No in-flight file was touched, the imports are acyclic, and TQBF's closure is unchanged.
- Both modules are wired into the `TuringMachine` facade.

**Layout.**

| Declaration | Meaning |
|---|---|
| `tableFields h es` | `h :: es.flatten`, the header then the entries' fields |
| `TableAt d r o h es` | the cells `[-2, L+1]` around origin `o` show `fieldsTape (tableFields h es)` |
| `TableWF m h es` | a nonempty header; every entry has `m` nonempty fields |
| `tableOffset h es j` | where entry `j` starts |
| `recordLength k n s` | `k(2s+1) + posWidth n + k + 4`, the length of every valid record |
| `recordTemplate Q T n s` | the bound field `bits (n+1)` and a window of `2s+1` cells |

- `TableAt` is anchored at an origin, not at the head, because find moves the head and append
  changes the table.
- `TableWF` keeps double blanks at the two ends only, so the seek rows apply.
- `tableOffset` has a closed form, and at `j = |es|` it is the second trailing blank, where
  `seekEndTM` stops.
- `recordTemplate` carries what a candidate record cannot reveal.
- `recordValid_iff_exists_cfg` is the bridge Savitch needs: valid records are exactly the
  records of windowed configurations on the actual input.
- `tableRewindTM` is the adapter, as a real machine: `skipBackTM` then `seekStartTM`,
  R2-seamed, with an exact contract (time `D + 7`).

**Rows.** Every row follows the §12.8 gate conventions:
- an existential module;
- `yes ≠ no` for two-verdict rows;
- a first-return time bound;
- an exact finish that restores every head, the input position, the scratch and the output;
- the work-space clause `∀ u ≤ t, ∀ j, |pos_u j − pos_0 j| ≤ C·(size + 1)`;
- fixed local tape layouts hosted by R1.

| Row | Finish | Time |
|---|---|---|
| `exists_inputLengthTM` | `Nat.bits \|x\|` at the output head | `C(\|x\|+1)` |
| `exists_fieldsCopyTM m` | the source's field layout at the destination head | `C(L+1)` |
| `exists_tableFindTM e m δ a₀ acc` (`0 < m`) | the first entry satisfying the fold predicate, by `findIdx?`: `yes` with the head on it, or `no` with nothing changed | `C(L_tab + \|w\| + 1)` |
| `exists_tableAppendTM m suf` | the table extended by one entry | `C(L_tab + L_e + 1)` |
| `exists_recordTemplateTM` | `recordTemplate \|x\| s` | `C(L_tpl + \|ws\| + \|x\| + 1)` |
| `exists_recordInitTM` | `cfgRecord s (Cfg.init q₀ x) τ₀` | `C(L + \|ws\| + s + \|x\| + 1)` |
| `exists_recordValidTM` | `yes` iff `RecordValid`, nothing changed | `C(L_fs + L_tpl + n + 1)` |
| `exists_recordNextTM` | `first`/`next` over an existential duplicate-free enumeration of exactly the valid records | `C ^ (L + L_tpl + 1)` |

**Decisions** (the design's Q1–Q9, as drafted; the user accepted the draft on 2026-10-11, and the statement gate audits them):

1. **Existential order.** The enumeration order of `recordNext` is existential. Savitch needs
   only a duplicate-free walk of exactly the valid records, and an explicit order would need
   a rank of `Option Q` and `T`, which no consumer reads. The fill uses the carry odometer.
2. **Fuel.** Find takes fuel `|es| < val w` and restores it, because the number of entries is
   on no tape and the only rich loop host needs a counter. A dedicated scanner would be a
   second forward trace, against decision 12.8.5.
3. **R8.5c's route.** It uses a dedicated framed counter whose carry writes `true` on the
   first non-`true` cell, the blank delimiter included. That is the counting phase of
   Catalog's private `f2_counterTM`, framed. The pair goes to the duplication ledger for the
   12.2c window. (§12.8a's "increment with width extension" fails, because `seekEndTM` stops
   one cell past the delimiter.)
4. **Validity time includes `n`.** No public row compares two words by `≤`. The bound
   `v ≤ n+1` uses the `Bool` `counterLoopTM`, lifted onto two digit tapes, at cost `O(n)`.
   Space stays `O(L + L_tpl)`.
5. **The three additions are rows:** `fieldsCopy`, `recordTemplate` and the adapter. There is
   no `tableMem` row; S1b keeps its inner loop.
6. **Homes** as above, with facade wiring at landing.
7. **Input convention.** The rows that read the native input enter at position `1` and
   restore it, as `inputCopyTM` and `inputFoldTM` do. Contrast `recordStepTM`, which saves and
   restores an arbitrary position.
8. **`recordNext`'s exponential bound** is honest: gaps between valid records are exponential,
   and `ComputesInSpace` needs only halting.
9. **The table rows are generic over `Γ`.** Find takes `e : Bool ↪ Γ` for its counter.

**Degenerate cases** (checked in the statements or executed by the probe):
- find at `m = 0` would be false, since `tableFields h [] = tableFields h [[]]`; hence `0 < m`;
- validity needs `|fs| = k + 3`, without which the verdict is not a function of the tape;
- the empty table;
- `T` empty: `first` answers `no` through `match`;
- `k = 0`, `s = 0` and `n = 0`.

**Consumers.**
- **S1b (§12.8a §4):** the template, the counters, the initial table, the round's find,
  copy, step, membership and append, and the verdict find.
- **Savitch:** the template, the start vertex, the midpoint enumeration, adjacency through the
  landed step and equality rows, and frame push and pop. Every frame is `O(S n)`.
- **The constructibility files:** `exists_inputLengthTM`.

**Fill dependencies.**

| Rows | Need |
|---|---|
| find and next | R8.0b |
| adapter, fieldsCopy and append | the Catalog Part-3 fill (delivered, PR #42) |
| template, init and valid | R8.5c and R8.6 |

Evidence: `campaign/gates/wave1-statements/evidence/S128bStatementsProbe.lean.txt`, which runs the design's
executed checks against the landed definitions.

### 12.9 Oracle-machine rows (landed 2026-10-11 with epoch B1; `Build/OracleCall.lean`)

**Why.** Every §12 row is plain-machine level, and the oracle model (`TuringMachine/Oracle.lean`)
had no run algebra. The B1 one-query constructions needed three capabilities: (i) a computation
captured onto the **query tape** and submitted; (ii) the four-state **answer tail**; (iii) a way for
plain contracts to drive an oracle machine.

**Rows.**

- In `Oracle.lean`:
  - the run algebra: `step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`,
    `runFrom_comm_of_step`, `ComputesInTime.mono`/`output_unique`;
  - the extraction contract: `queryString_length_le_of_blank` (C1-P1) and `queryString_eq_of_cells`;
  - **the transfer bridge** `runFrom_eq_plainEmptyOracle`, after `runFrom_eq_of_forall_ne_qQuery`.
    On a run segment that avoids `qQuery`, the oracle run is the run of the plain table
    `plainEmptyOracle`, so host-parametric plain contracts apply unchanged.
- In `OracleFinite.lean`: the bundled `mono` and `output_unique`.
- In `Build/OracleCall.lean`:
  - `queryString_bufferTape`;
  - `answerAction`, with `step_of_qQuery`, `step_of_answerAction` and `runFrom_two_of_qQuery`;
  - **query capture** `capture_reaches_qQuery`: W1 with its return state taken to be `qQuery`.
    W1 writes on the host's last tape, which is the query tape.
- In `Finite.lean`, the shared guard discharge: `MultiTapeTM.exists_first_halt`.

**Consumers.**

- `mem_POracle_of_polyTimeReducible`, and through it the `SAT`-oracle corollaries and
  `EXP_subset_POracle_EXPCOM` (B5);
- `unaryWitnessLang_mem_NPOracle`, using the tail through `OracleNDTM.fixChoice`;
- `compl_mem_POracle`, using `runFrom_comm_of_step`.

**Not yet here: oracle-call hosting.** This is a plain host simulating an oracle machine that runs
a decider on the extracted query word. It is the library gap behind `POracle_eq_P_of_mem_P`
(deferred) and B5's `NPOracle_EXPCOM_subset_EXP` dispatcher. Its rows need a design note and a
statement gate:

- the headline simulation;
- the private clean call of `ClassNP/EXP.lean` promoted, without the native-input rewind;
- origin tracking for the query tape;
- query extraction with cell `-1` saved;
- the dispatch host.

The draft headline statement, `FinOracleTM.exists_plain_simulation`, is recorded in
`campaign/fills/b1/integration/b1-integration.md`. **Designed and stated in §12.10** (2026-10-11).

### 12.10 Oracle-call simulation (statements landed 2026-10-11; design W2, route and homes accepted by the user)

**Why.** §12.9 records the gap, "not yet here: oracle-call hosting". No public row lets a
plain host simulate an oracle machine by running a decider on each extracted query. Two
targets are blocked:
- B1's last, `POracle_eq_P_of_mem_P`;
- B5's summit, `NPOracle_EXPCOM_subset_EXP`, and through it three `EXPCOM` identities and
  `baker_gill_solovay`.

**The decision: one trace, and nondeterminism by choice words.**
- **The deterministic row is the only oracle-call simulation trace.** It is a plain host that
  answers each query by a clean call of the decider.
- **The nondeterministic form is a reduction, not a second simulation:**
  1. the choice-word machine determinizes the oracle NDTM along a word on a work tape;
  2. the deterministic row simulates it;
  3. the plain certificate shell and the proved `exists_proj_decider` enumerate the words.

  The total is `2^O(p)`.
- **Branchwise simulation is rejected.** Branches would consume choice bits through every
  decider run, so the only public determinization would enumerate doubly exponentially many
  words. Avoiding that needs a sparse-guess row, which is a second trace under another name.
- **Virtual input stays at the plain level, after the simulation.** An oracle machine has one
  `qQuery` state, so an oracle-level Z1 would re-prove Z1's lockstep. This forces the
  deterministic row to be stated **from preloaded starts**. The `initCfg` form, the B1b draft
  headline, is a proved corollary.

**Rows.**

| Module | Declaration | Status |
|---|---|---|
| `Build/OracleSim.lean` | `FinTM.prefixWords` (+ `_nil`, `_update`), `Cfg.init_eq_ofWords`, `OracleTM.queryString_runFrom_length_le_of_blank` (W2-0) | proved |
| | **`FinOracleTM.exists_plain_simulation`** (W2-S): from any preloaded start, a plain host reproduces the oracle machine's halting output within `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(\|query_r\|)` | **proved** (fills-4 to fills-6; wave-1 fill gate closed 2026-10-12) |
| | `…_of_monotone`, `…_initCfg`, `FinOracleTM.exists_plain_decider` | proved from W2-S |
| | `FinOracleNDTM.choiceOut`, `choiceOut_eq_true_iff`, `mem_iff_exists_choiceOut` | proved |
| | **`FinOracleNDTM.exists_choiceTM`** (W2-C): the choice-word machine, `≤ 2\|u\| + 2` steps, the same queries, except that at exhaustion in the query state one query may be submitted and its answer discarded (statement gate, minor 4) | **proved** (fills-4) |
| `Build/CertShell.lean` | **`FinTM.exists_certificateShell`** (W2-V): the plain shell deciding `{x ++ u \| \|u\| = C(\|x\|+1)^c ∧ out x u = [true]}` | **proved** (fills-4) |
| | `FinTM.certificateShell_proj` | proved |

- The exact sum, "`T_D` of the query lengths", needs no monotonicity.
- Both instantiations follow from the monotone corollary:
  - polynomial `τ` gives `P^O = P`;
  - exponential `τ`, at a polynomial-time machine, gives `P^EXPCOM ⊆ EXP`, and the summit
    follows through W2-C.

**Fill routes** (binding sketches in the docstrings).
- **W2-S:**
  - the source's tapes, a shadow tape tracking the query head's side of the origin, the Z1
    bank of the clean call `exists_installCallTM`, and a scratch tape;
  - off `qQuery`, the bridge `runFrom_eq_plainEmptyOracle` plus Z5;
  - at `qQuery`, nine R2-seamed phases: bookmark, origin walk, save and blank cell `-1`,
    `copyTM`, the Z1 call at `y = []`, read the verdict, restore, walk back, answer.
  - **As delivered** (fills-6; documented in the target's appendices, and confirmed sound and no
    weaker by the wave-1 fill gate): the host `oracleHost` is **one public phase host**
    (`phaseHostTM`), with a single R2 seam between the public copy and the relocated call
    (`oracleService_run`). Preparation takes at most `natAbs p + 3` steps and restoration
    exactly `natAbs p + 3`, for both signs of the displacement and for zero. A query costs at most
    `2·|p| + 2·|z| + tCall + 13`, redirects included.
- **W2-C:** lockstep by induction on `u`, in the `toOracleNDTM_runWith` shape. An exhausted
  word answers `false`, so an unhalted branch never shows `[true]`.
- **W2-V:** the native-input call R8.5e (`exists_inputCallTM`) at `splitSolve`, then Z1 inside
  the **returning** R1 capture, then a three-state scan. R8.5e is proved at the tip since PR
  #41, so W2-V's route cites no sorried row.

**Decisions.** The user took the first and third (2026-10-11); the rest are as drafted and
go to the statement gate.

1. **The route:** one trace, choice-word enumeration, no branchwise row.
2. **W2-S in preloaded generality,** with the `initCfg` form derived.
3. **W2-V in its own plain module,** `Build/CertShell.lean`, keeping plain consumers off the
   oracle module. Deduplicating the private 2B shell in `ntime_poly_subset_NP` is the shell's
   second customer, a 12.2c item.
4. **W2-C is public here.** It is the core of a relativized Theorem 2.6. It has one named
   customer, against the rule of admission's two.
5. **Time only.** The oracle layer has no space measure. This is flagged against the §12/§13
   space mandate.
6. **Sequencing.** W2-S and W2-C can be filled at once; W2-V's sorried dependency is gone.

**Mirrors, factored** (disclosed at landing; factored in round 2 of the wave-1 statement gate,
2026-10-11, user decision; `campaign/gates/wave1-statements/resolutions.md`):
- W2-0 and the private invariants `runFrom_workTapes_invariant` (`Oracle.lean`) and
  `runWith_headBlank` (`OracleNondeterministic.lean`) now all specialize the promoted
  `OracleTM.step_radius`/`OracleTM.runFrom_radius` (`Oracle.lean`).
- `certificateShell_proj` and `Nondeterminism.lean`'s split callers cite
  `append_split_unique` with `certificateLength_strictMono` or
  `expCertificateLength_strictMono` (new module `ChoiceWords.lean`). The private split lemmas
  are deleted.
- `mem_iff_exists_choiceOut` and `Nondeterminism.lean`'s acceptance argument share
  `choiceBudget_le` and `run_take_of_halted` (`ChoiceWords.lean`).

**Consumers** (derived in `campaign/gates/wave1-statements/evidence/S1210StatementsProbe.lean.txt`):
- `POracle_eq_P_of_mem_P`, which rests on W2-S alone;
- `NPOracle_EXPCOM_subset_EXP`, the summit;
- `baker_gill_solovay`.

Each is `rfl`-identical to its campaign statement, as are the three `EXPCOM` identities the
probe also derives. The probe's deterministic inclusion `POracle_EXPCOM_subset_EXP'` is
probe-local: it is derived from W2-S directly and has no campaign counterpart.

B5's own `exists_EXPCOM_decider` (home `Diagonalization/EXPCOM.lean`) is the summit's
query dispatcher. It is a B5 obligation, not a §12.10 row.

### 12.11 The format-parameterized code simulator (B5a; statements landed 2026-10-11; headline H1 by user decision, H2 in the backlog)

**Why.** Plan §4e decision 2: "B5 builds one format-parameterized uniform interpreter and
discharges ZF-B4, on top of 12.2c item 8's parameterized parse layer".
- `Universal`'s interpreter is hard-wired to one work tape, and is already copied once inside
  `Universal.lean`.
- ZF-B3's layer in `Codes2Tape` is format-specific and contains no interpreter.
- `CodeFormat` has no machine semantics.
- The two target files cannot host a layer for each other: EXPCOM's closure contains neither
  CounterLoop nor VirtualInput, and Codes2Tape is not imported by EXPCOM.

Hence a pre-issue statement module.

**Rows** (`TuringMachine/CodeSimulator.lean`).
- **`Turing.MachineFormat extends CodeFormat`** adds:
  - a work-tape count `k`;
  - a semantics `machine`;
  - two laws: `serialize_eq`, the fixed `k`-record serialization `serializeK`, and
    `skipTable_eq`, the fixed skipper `codeSkipTableK k`.
- **The generic writer layer:** `workReadsK`, `tableBitsK`, `serializeK`, `codeSkipTableK`,
  with proved bridges `tableBitsK_two` and `codeSkipTable2_eq_codeSkipTableK` to the frozen
  two-tape writers.
- **`oneTapeMachineFormat`,** public and proved. Its `decode` is `codeDecode`, and its
  machine is `CodeTM.toFinTM`, both by `rfl`.
- **`MachineFormat.exists_polyCanonizer`** (sorried): one machine computing
  `F.serialize (F.decode α)` in polynomial time. It serves the simulator's front end, the
  `canonizer` field of both uniform schemes, and, off-batch, the TMSAT concrete-scheme
  canonizer.
- **`MachineFormat.exists_uniformSimulator`** (sorried), **H1**. On
  `⟨⟨bits t, α⟩, x⟩` it answers `[true]` iff the decoded machine computes `[true]` on `x`
  within `t` steps, and `[false]` otherwise, within `d·(|α| + |x| + t + 1)^d`. This is
  field-for-field the shape of `UniformMachineCode.simulator_accepts`/`_rejects` and their
  `…2` mirrors.

**Inside H1:** exactly one private interpreter trace, a step block for one simulated
transition of a `k`-tape coded table. It is hosted by §12.7's `counterLoopTM` and Z1's
`vhostEmitTM`, built from the §12 layer, and is not a copy of `universalInterpreter`. Its
properties:
- states independent of the code;
- per-round cost `c·(|β| + 1)`, independent of `t` and `x`;
- input read only through its own head;
- silent;
- proved at the relation level.

Per-round cost independent of `t` and `x` lets stage 1, B6 and the NTIME deterministic core
reuse it under different hosts.

**Instances** (B5a fill):
- **EXPCOM:** `exists_uniformMachineCode` at `oneTapeMachineFormat`.
- **ZF-B4:** `exists_uniformMachineCode2` at a private two-tape format in `Codes2Tape`, whose
  laws are the two bridges.

The two assemblies are a forced mirror pair, as their target structures are. Both are
assembled from H1 in `campaign/gates/wave1-statements/evidence/B5aStatementsProbe.lean.txt`, resting only on the
two contracts. **NDCodes is not an instance:** ND codes denote NDTMs and need no interpreter.
A separate small parse-layer rider can handle them.

**Decisions** (from the dossier's D1–D9):
- **D1 (user, 2026-10-11).** A pre-issue statement phase. It is landed by the combined
  statement PR, under one gate.
- **D3 (user, 2026-10-11).** Headline **H1** for now. **H2** is per-code linear,
  `d·(|α|+1)^d·(t+1)` with no `|x|` term. It would serve stage 1 directly, but forces
  in-place suffix input and a suffix-input host that does not exist. H2 is recorded in
  `backlog.md`, and its corollary to H1 is proved in the probe.
- **D2 and D4–D9 are fill-brief matters**, settled when the B5a brief issues. The dossier
  recommends route Z, the generic interpreter at `k = 1`, for EXPCOM, with route W
  (Universal plus a post-processor) as an escalation fallback only. It also recommends moving
  ZF-B3's semantic layer into `CodeSimulator`, generalized, and deleting the dead ZF-B3
  privates.

**Forced writer pairs.** The generic `tableBitsK` reproduces part of the frozen writers'
text. The statement screen gives three such pairs: `oneTapeFormat` at 85%, `codeTable2Bits`
at 67% and `Code2TM.serialize` at 56%. The frozen bodies cannot be redefined, and
`tableBitsK_two` proves the equalities. This is item 8's pre-named residual watch item.

## 13. The zone and virtual-input layer (proposed 2026-10-09, post-§12 close)

**Mandate** (user direction 2026-10-09, at the §12 fill-campaign close —
track A of the two parallel tracks, the other being the chapter-1/2
retrofit): the §12 scope note **R9 promoted**. R9 drew the line at
physical-tape selection — `ι` relocates whole tapes and "the Hennie-Stearns
and universal-machine consumers get their zone/virtual-input representation
layers separately" (`Build/Embed.lean` header). This increment is that
separate layer. It gates the two stage-1 builds (the Hennie-Stearns `k`→2
conversion and the two-work-tape universal machine, plan §2.1/§4b) and is
scoped, like §12, beyond its first consumers: the virtual-input half serves
the `NP^EXPCOM ⊆ EXP` summit and the 12.2c dedup, and the zone half is
shaped so the chapter-1 Robustness conversions can gain **space theorems
additively** (plan §2.7's fallback route to Ex 4.1/Thm 4.8). §12's space
mandate continues: **every item carries a space clause alongside its time
cost** (`Turing.MultiTapeTM.spaceUsed`, work tapes only).

**Evidence.** The virtual-input pattern has now been hand-built four times
over the proved corpus: the A2 forwarding controller's
`a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` lockstep (15 of
its 45 privates; both boundary clamps, empty-word case, halt absorption —
all proved), F2A's `f2_splitCountAction`/`f2_splitCount_run`
(virtual *empty* input over preinstalled banks), the universal
interpreter's prefix-input discipline, and the oblivious candidate's
`obliviousVisit` virtual-tape transduction. All four sit on the same public
primitive — `virtualMove`/`VirtualTag`/`virtualNextTag` and
`bufferTape_inputSymbol` (`Simulation.lean`) — and each rebuilt the hosting
and lockstep privately. On the zone side, the in-repo precedents are the
`SingleTape.lean` multiplexing encoding (`SweepCell`/`tapeRow`) and
`ObliviousSetup.lean`'s guide-zone layout with its two-directional run
identities; what does not exist anywhere is a *reusable* zoned carrier with
shift routines. The F2 epoch audit's three optional regression corollaries
(zero-time startup, both virtual-input clamps, setup followed by an
emitting halting step) are adopted here as permanent lemmas of Z1.

**What already exists and is consumed, not duplicated**: the §12 layer
itself (R1/R2 and the catalog rows are the assembly language of every
construction below); `virtualMove`/`VirtualTag` (`Simulation.lean`);
`Turing.actionBits₂` and the `CodeNDTM` two-work-tape serialization
(`NDCodes.lean`, statement-frozen under the closed P3.3 gate) — Z3 builds
the deterministic sibling against the same record format, never a second
serialization; `UnaryTape.lean`; the harvest policy of §8 (reimplement
against the ABI with the original proof as template; audited originals stay
in place until the separately-tracked retrofit/12.2c dedup).

### Z1. Virtual-input hosting (the `a2_mapVirtual` pattern, promoted)

A transformer hosting a machine whose input is a **designated buffered
word** rather than the native input: given a host with an injective tape
selection (R1's `ι`) plus one buffer tape holding `y`, the hosted machine
runs with `y` as its virtual input, buffer head at
`source.inputPos - 1` under a `VirtualTag` boundary discipline. Spec shape:

* **lockstep** — one host step per source step, transported `runFrom`
  identity (the A2 `a2_mapVirtual_run` shape, generalized from its
  two-buffer controller to the R1 selection);
* **clamps** — both boundary clamps hold with **no nonempty-`y` premise**
  (empty `y`: position `0` is the right boundary, `-1` the left; outward
  moves stay, inward moves cross) — the binding A2/F2 audit contract;
* **halt absorption** — the source's halting action executes before the
  host control dies; later times are fixed;
* **emission policy** — suppressed or forwarded, mirroring R1's two modes
  (open decision 12.4 resolves both at once);
* **time** — exact; **space** — coefficient-one containment: each selected
  tape's host visited set is contained in the source's visited set on `y`
  at the same horizon (the R4 ledger shape, proved in `a2_map_space`).

Permanent regression lemmas (audit-adopted): the zero-time startup
instance, the two empty-`y` clamp instances, and the setup-then-emitting-
halt seam. Generic form of: `a2_mapVirtual*` (A2), `f2_splitCount*` (F2A,
the `y = []` specialization), the universal interpreter's input phase, and
the query simulation every oracle-summit machine will need.

**Z1 rider — the R1 selected-tape exports (decision D-R1, user
2026-10-09, from the retrofit inventories, plan §4d).** The three retrofit
inventories independently identified the same R1 API gap: `Embed.lean`
exports no selected-tape field lemmas (`embedSlot_selected`/`_unselected`
are private) and no agreeing-host lockstep, so no old-code R1 consumer can
be proved from the public surface. This statement phase adds, **additively
in `Embed.lean`** (shared-file mechanism, audited under this gate): public
selected-tape projections of `embedSilentCfg`/`embedEmitCfg` (contents and
head of tape `ι i`), and an `ofWords` transport form. Unlocks the blocked
Hardness families (M/N/AM/U, Z/AB/AG — ≈ 300-350 lines) at the next
retrofit window.

### Z5. Machine-agreement transfer (decision D-R3, user 2026-10-09)

A general lockstep-transfer lemma, the `hagree` genre of
`capture_run`/`emit_run` made standalone: two machines over the same tape
count and state type whose transition tables **agree on a set of states**
run identically, configuration for configuration, from agreeing starts for
as long as the run stays inside the agreement set; a guarded variant takes
the agreement hypothesis per reachable state. Natural home:
`Simulation.lean` beside the existing lockstep gadgets (placement open
decision 13.5: Simulation versus a `Build/` module). Customers (rule of
admission): the Loop forwarding host (H3's 14 verbatim re-proved phase
lemmas, ≈ 550 lines, collapse to one transfer — `emLoopHost` agrees with
`loopHost` on every non-body state); the 13 guarded `clSlot_run` agreement
sites in `CookLevin/Hardness.lean`; every future mode-variant host (the
§12 loop hosts' decision/find/emit triplet is exactly this pattern).
Estimate: ≈ 4 points spec + fill; the risk is quantifier placement on the
agreement set, not proof content.

### Z2. Zoned tape carrier (the Hennie-Stearns representation)

The representation of `m` virtual work tapes on **one** physical tape with
amortizable locality: a `ZoneLayout` (level count `ℓ`; per-level zones
`L_i`/`R_i` of capacity `2^i` around a home origin, [AB09] §1.7) and a
carrier predicate `ZoneCfg` relating one physical word to `m` virtual words
plus per-zone fullness states (empty / half / full). The layer owns:

* **the carrier** — `ZoneCfg` well-formedness, read/write-at-home
  contracts (the virtual heads always sit at the physical origin), and the
  cell-encoding convention (open decision 13.2: how `Option Bool` virtual
  cells embed into binary physical cells — paired-cell presence/data
  tracks, with `SingleTape.lean`'s `SweepCell` encoding as the precedent);
* **the shift routines** — per-level `shiftIn`/`shiftOut` rebalancing
  rows with **exact** costs `O(2^i)`, assembled from R3
  transfer/copy/clear via R2 seams, each with its space row (visited cells
  within the touched zones);
* **the cardinality lemmas** — visited-set bookkeeping for multiplexed
  tapes: physical space bounded by the sum of touched zone extents, the
  piece the Robustness space annotation (Z4) consumes.

Explicitly **on top, not inside**: the `2^i`-fullness invariant across a
run, the amortized `O(T log T)` charge, and the simulation theorem itself —
those are the Hennie-Stearns consumer's mathematics (plan §2.1), as the
§12 precedent kept the loop ledgers out of the loop host. Scope note:
Z2 is sized for the H-S discipline (one zoned tape + one scratch tape);
a general `k`→`k'` conversion is not in scope.

### Z3. Two-work-tape codes (the deterministic `actionBits₂` sibling)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`EffectiveMachineCode`/`UniformMachineCode`,
`Encoding.lean`), which is why Thm 3.1 arrives at `f²` (plan §2.1). Z3
extends it: a deterministic two-work-tape code scheme over the
**same `actionBits₂` record format** as `CodeNDTM` (one branch instead of
two), with the `CodeParser` extension and the `UniformMachineCode`-style
uniform-decoding clause (the P3.2 lesson: variable-code consumers need the
uniformly-timed form). The two-work-tape **universal machine itself** is
the stage-1 consumer build, not part of this layer; Z3 ships the codes it
reads. Space rows on the parser rows from the start.

### Z4. Space annotation for the Robustness conversions (consumer-driven)

Additive `spaceUsed` theorems for the chapter-1 conversions
(`one_work_tape`, the alphabet reduction) via Z2's cardinality lemmas — no
signature changes, the audited surface untouched (the R3 retro-annotation
precedent). This is plan §2.7's fallback route to the space-efficient
universal (Ex 4.1, Thm 4.8). **Design-time obligation, recorded here**: at
the Z1-Z3 spec phase, assess whether the two-work-tape universal carrying
Z1/Z2 space rows yields Ex 4.1 directly; the answer (and hence whether Z4
is needed at all, and at which strength) is recorded before the statement
gate, so the chapter-4 risk register (§6 summit 1) is settled either way.

### Consumers (rule-of-admission check, §4: two named customers per item)

| Item | Customers |
|---|---|
| Z1 virtual-input hosting | the two-work-tape universal (stage 1); the `NP^EXPCOM ⊆ EXP` summit's query simulation; the 12.2c dedup of `a2_mapVirtual*`/`f2_splitCount*`; the P3.3 universal-NDTM fill's code/input discipline |
| Z2 zoned carrier + shifts | the Hennie-Stearns `k`→2 conversion (plan §2.1); the Robustness space annotation (Z4); the Ex 1.6 oblivious sharpening (recorded stretch goal, `Robustness/Oblivious.lean`) |
| Z3 two-work-tape codes | the two-work-tape universal; the Thm 3.1 re-derivation at `f log f` (Hydroxyi's diagonal argument over the new codes) |
| Z4 space annotation | Thm 4.8/Ex 4.1 fallback (plan §2.7); `L ⊊ PSPACE`/space-hierarchy fills (P4.3) if the universal route stalls |

### Placement, sequencing, cost

* New files `Build/VirtualInput.lean` (Z1) and `Build/Zone.lean` (Z2),
  namespace `Turing.FinTM`, order list after `Build/Catalog`; Z3 as a new
  `TuringMachine/Codes2.lean` beside `Encoding.lean` (placement open
  decision 13.3: a new file versus extending `Encoding.lean` — the frozen
  audited surface of `Encoding.lean` argues for the new file); Z4 lands
  additively in the `Robustness/` files through the shared-file mechanism,
  flagged for its own audit.
* Process per `workflow.md`, the §12 precedent verbatim: maintainer-serial
  spec layer (quantifier-sensitive), statement gate by external audit,
  fills as briefed batches with exclusive ownership, epoch-boundary fill
  audit. The gate must close before the H-S/two-tape-universal builds
  start; chapter-3/4 fill briefs written while this layer is open simply
  do not cite it (the EXPCOM brief prefers Z1 only if Z1 is closed).
* Estimate (campaign points): Z1 ≈ 8 (harvest-grade — the lockstep is
  proved four times over; the risk is quantifier hygiene, not proof
  content), Z2 ≈ 14 (genuinely new; the carrier predicate is the risk
  concentration, L-style), Z3 ≈ 6 (format fixed by `actionBits₂`), Z4 ≈ 6
  (retro-annotation against Z2's lemmas). Total ≈ 34, between the §12
  statement layer and one fill epoch.
* **Citation duty** (binding, the 2026-10-06 guideline and the 2026-10-08
  citation-audit row): the design adapts [AB09] §1.7 (Hennie-Stearns) and
  Exercise 1.5/1.6; the §12 duty extends here — Édouard Bonnet's
  lax-434930 `classical-complexity` (Apache-2.0, commit `0c084031…`) is
  cited in this addendum, the module docstrings, and the blueprint entries
  wherever its stack-machine routine catalog informed a row's shape; no
  external code is imported or transcribed.

### Open decisions (13.x, for the user at spec time)

1. **13.1 Zone discipline**: zones-with-fullness (the [AB09] §1.7 layout,
   proposed) versus plain interleaving (simpler carrier, no amortized
   locality — insufficient for H-S alone, but cheaper if Z2's only
   customer were Z4). Proposed: zones; interleaving is not built.
2. **13.2 Cell encoding**: how `Option Bool` virtual cells embed in binary
   physical cells (paired presence/data cells proposed; `SweepCell` as
   precedent).
3. **13.3 Z3 placement**: new `Codes2.lean` (proposed) versus extending
   the frozen `Encoding.lean`.
4. **13.4 Z1 mode shape**: one transformer with an emission-mode parameter
   versus two transformers — inherits open decision 12.4's resolution.
5. **13.5 Z5 placement**: the agreement-transfer lemma in `Simulation.lean`
   beside the lockstep gadgets (proposed) versus a `Build/` module.


### 13a. Decisions resolved; epoch structure (user, 2026-10-09)

All five open decisions resolved as proposed, with one rename:
**13.1** zones-with-fullness (interleaving is not built); **13.2** paired
presence/data cells (`SweepCell` precedent); **13.3** a new file, renamed
**`TuringMachine/Codes2Tape.lean`** so the "2" reads as *two-tape*;
**13.4** Z1 inherits 12.4's resolution (a silent/emit transformer pair over
one shared core); **13.5** Z5 lands in `Simulation.lean`.

**The statement phase runs in two tranches, each with its own gate:**

* **A-S1 — the virtual-input half**: Z5 (the agreement transfer,
  `Simulation.lean`, additive), Z1 (`Build/VirtualInput.lean`, new), and
  the Z1 rider (the R1 selected-tape exports, `Embed.lean`, additive via
  the shared-file mechanism). Rationale: harvest-grade risk (the lockstep
  is proved four times over; the rider's facts are proved privately), and
  its consumers are the *near-term* ones — the blocked retrofit R1
  families, the 12.2c dedup, the Loop H3 collapse, the EXPCOM summit.
* **A-S2 — the zone half**: Z2 (`Build/Zone.lean`), Z3
  (`Codes2Tape.lean`), Z4 (the Robustness space annotation). Rationale:
  Z2's carrier predicate is the genuine design risk and deserves an
  undiluted gate; its consumers (Hennie-Stearns, the two-tape universal)
  sit one stage later. The Z4 design-time obligation (does the two-tape
  universal's space bonus yield Ex 4.1?) is discharged in the A-S2 pack.

The canonical Z1 shape (spec-time refinement, recorded before drafting):
the transformer is defined on exactly `1 + M.k` work tapes — the buffer
first, the payload bank after it — and **relocation is not baked in**:
a consumer needing the buffer or bank elsewhere composes with R1. One
shared hosting core; `silent`/`emit` flavors per 12.4; the tag lives in
the transported control state (the `a2_MapState.run q tag` precedent).

### 13b. A-S1 gate close (2026-10-09, after `campaign/gates/vhost-infra/findings.md`)

Round-1 **PASS, 0 blockers / 0 majors / 2 minors**; loop summary
`campaign/gates/vhost-infra/resolutions.md`. Minor sweep recorded here per the
audit's proposed fix (A-S1-2): the Z1 rider's promised **`ofWords`
transport form is supplied by specialization** of the four delivered
selected-tape projections (instantiate `c := Cfg.ofWords …`); no
separately named specialization is exported now — if a consumer wants the
whole-configuration identity (with its frame, capture, head, and output
parameters spelled out), it is commissioned on need at the 12.2c window.
A-S1-1 (the pack under-counted the definitions: eight with
`MultiTapeTM.AgreeOn`, 23 audited declarations) is acknowledged as a pack
erratum; shipped packs stay verbatim. The audit's four recommended sanity
exports (initial-tag validity + `q₀`-independence, fixed-parameter
transport injectivity, native-head constancy for arbitrary host
configurations, named boundary/seam specializations) are **adopted as
optional permanent lemmas of the A-S1 fill brief** — offered, not
required. The audit's Z5 composition-of-responsibilities reading is
affirmed and binding on retrofit consumers: Z5 equates runs on one
carrier; heterogeneous `clSlot_run`-style sites first transport
(R1 + state renaming), then agree — a public guarded
configuration-transport theorem is a possible later export, not promised.

### 13c. A-S2 round-1 repairs (2026-10-09, after `campaign/gates/zone-infra/findings.md`)

The A-S2 statement gate returned **FAIL: 1 blocker, 1 major, 2 minors**;
repairs landed with the round-2 pack:

* **A-S2-1 (blocker) → the inward room premise removed and the wrappers
  split.** The spec had one shared room hypothesis on both shift
  directions; inward shifts *remove* donor cells, so a full donor — the
  exact classical case — was illegal, and the audit's full-chain family
  showed the delivered interface forcing `Ω(T²)` behavior. Repair:
  `zoneShiftInW` carries no room condition; `zoneShiftOutW`'s receiving
  room moved **inside its guard**; the contents wrappers are the
  hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the
  guarded-total `zoneMove`; and the audit's required gate material landed —
  the full-donor regression (`zoneShiftInW_full_donor`) and the cascade
  statements (`zoneCascadeRight` with its represented-word, length, and
  geometric-cost lemmas), whose proofs adopt the audit's schedule analysis
  as the binding route. The rows now realize the **total guarded
  operation, identity branch included**.
* **A-S2-2 (major) → the Z4 one-tape sketch replaced.** The received
  `sweepTM` grows its window unconditionally (the audit's stationary-head
  scanner refutes it as a witness); the statement stands, and the binding
  route is now a **demand-grown** sweep witness with the audit's
  union-of-origin-intervals bound, interleaving factor, and the
  all-`Γ'`-inputs retraction (empty-alphabet and zero-tape cases named).
* **A-S2-5 (note, adopted) → the Ex 4.1 assessment stands as a
  *design-level* verdict, not an implementation discharge**: the stage-1
  universal must specify a space-accounted input interface (native/suffix
  access or an accounted buffer — a materialized input copy costs
  `Ω(|x|)` work cells, absent from the sketched ledger) and a parser with
  its own space ledger; the uniform scheme (Z3), not an arbitrary
  effective scheme, is what a space-accounted canonizer route would use.
* Minors: the pack's definition count corrected (22, not 25; inventory in
  the findings); the module's export list and the guard semantics
  docstrings corrected in place (A-S2-4).

### 13d. Revision: the zone layer at the book's design (draft, 2026-10-10)

**Status: design draft for user review. No Lean change has been made.**

**Process rule (user, 2026-10-10, binding for this revision).** Every Lean change
that results from this revision goes through **both** human approval, as a PR
the user merges, **and** a separate audit gate. Nothing is pushed directly to
the campaign branch. This covers the library generalization (G1), every new
statement phase, and every fill.

#### Why

ZF-A3 (`zone-f1-A3.zip`, held and not integrated) proved infrastructure only:
a geometric counter schedule, counter-driven navigation, a counter built from
the unary level, a window readout, and counter removal, 952 lines in all.
Neither shift machine was proved. A comparison with [AB09] §1.7 traces the
cost to four of our choices, not to the mathematics:

1. **A supplied level with pairwise shifts.** Each pairwise shift starts from
   home, so the machine must count its way to level `i`. In [AB09] the index
   `i₀` is *discovered* by scanning outward, and one sweep does all the work
   between adjacent zones where the head already is.
2. **No markers.** A binary physical tape carries no zone boundaries, which
   forces the binary counter.
3. **Catalog reuse on packed zones.** The generic routines need a blank on
   each side of a word, but packed zones abut, hence the save, blank, call,
   restore cycle around every call.
4. **Exactly two tapes per row,** so the counter shares the scratch tape with
   the level word.

There is also a **gap independent of the controller**. Plan §2.1 specifies
the book's route ("parallel tracks, buffer zones of size `2^i`, amortized
shifts"), but `ZoneContents` holds **one** simulated tape, and both rows
operate on a tape dedicated to it. In a two-tape simulator only one tape can
be zoned, so the present carrier serves only machines with one work tape,
and Hennie–Stearns needs each of `k` tracks to shift independently.

#### Decisions taken (user, 2026-10-10)

- **A rich alphabet, finished by alphabet reduction.** The Hennie–Stearns
  simulator is a two-tape `FinTM Γ` over a large alphabet `Γ`, as in [AB09]
  via Claim 1.5, and the public `Turing.FinTM.alphabet_reduction`
  (`Robustness/AlphabetReduction.lean`) finishes it. That theorem preserves
  the work-tape count (`M'.k = M.k`), costs `3(|Γ|+1) + 2` steps per source
  step, and is stated at the function level (`ComputesFunInTimeVia e f T`
  gives `ComputesFunInTime f (c·(T+1))`). A space form exists
  (`alphabet_reduction_spaceUsed`).
- **Option (b): generalize the library to arbitrary alphabets** rather than
  building a parallel `Γ`-only toolkit. Large-alphabet machines will recur.

#### Components

**G1. Alphabet-generic library (in place).** Change `Bool` to an arbitrary
`{Symbol : Type*}`, with `DecidableEq` where needed, in:

- **`Build/Seam.lean`:** `seamCompTM`, `seamReleaseTM`, and their
  general-configuration theorems (the `_ofCfg` trio and the release pair).
  The canonical `Cfg.ofWords` theorems stay Bool-specific and become
  instances of the general ones.
- **`Build/Embed.lean`:** the transformers, transports and all their
  theorems, including the RB5 state-transport lemma. The capture tape's
  buffer generalizes with `bufferTape`.
- **`FinTM.bufferTape`** (`Simulation.lean`): from `List Bool` to
  `List Symbol`. The definition is unchanged.
- **The R3 sweep rows in `Build/Catalog.lean`:** `transferTM`, `copyTM`,
  `clearTM`, `compareTM`, and their §12.6 framed contracts. Their tables
  never inspect a symbol's value except for equality, so they generalize.
  `incrementTM`, the canonical rows and the Part 2 space rows stay
  Bool-specific.

**Binding constraint:** every existing Bool statement either keeps its
statement verbatim or becomes a definitional instance at `Symbol := Bool`
that its consumers elaborate unchanged. The full downstream replay is the
evidence. This is a change of audited public signatures, so it gets **its
own gate**, before anything consumes it.

**G2. Mapped sweeps (new, alphabet-generic catalog rows).** Per-track
shifting moves one *component* of each cell and leaves the other tracks in
place, which whole-symbol copying cannot do. The rows are `copyMapTM` and
`transferMapTM`, parameterized by `extract : Γ → Δ` and
`merge : Γ → Δ → Γ`: they write `merge (dst cell) (extract src cell)`. Their
framed contracts follow the §12.6 shape (exact time `2|w| + 2`, finish
configuration, no earlier exit, trajectory). At `merge := fun _ s => s` they
are the plain rows. This is the reusable large-alphabet primitive. Its proofs
must share the generalized R3 trace, not copy it (one trace per routine
family, as §12.6 established). **Decision (user, 2026-10-11; the §12.8
statement gate's Q7).** G2's one-tape core is `scanTM` (§12.8a).
`copyMapTM`/`transferMapTM` stay, for the cross-tape G3/G4 consumers. Their
`merge` takes `Option Γ → Δ → Γ`, so that blank destinations are admitted,
and they share one trace with the scan.

**G3. The multi-track zoned carrier over `Γ`.**

- **Alphabet:** `ZoneSym k := Bool ⊕ ZoneCell k`, where
  `ZoneCell k := Fin k → Option (Option Bool)`. Per track, `none` is the
  buffer symbol `⊠` (an unoccupied slot) and `some v` an occupied slot
  storing the virtual symbol `v`. `Sum.inl` embeds the binary input and
  output (the `e` of `ComputesFunInTimeVia`). It is finite, so it is a
  `Fintype`.
- **Contents:** `Fin k → ZoneContents ℓ`. **The pure layer is reused
  verbatim per track:** the codec is unneeded, but the layout arithmetic,
  `ZoneContents`, `zoneSlot`, `zoneSide`, the pairwise ops and their
  word-preservation lemmas, the head steps, and the cascade with its
  lemmas all carry over.
- **Layout:** one physical cell per virtual slot, holding the whole tuple,
  with the home at cell 0 and **one blank separator cell between consecutive
  zones** on each side (decision 13d.1). Each zone is then a blank-delimited
  nonblank word of length `zoneCapacity i`, so the generalized framed sweeps
  (G1, G2) apply directly, with **no save/restore**. The separators also mark
  zone boundaries, so **no counter** is needed.
- **The home cell** holds all `k` tracks' virtual symbols, so the simulator
  reads and writes the virtual heads in one step.

**G4. Rebalance rows.** For a direction `d` and a track `t` (`t` in finite
control, since `k` is fixed for a given simulated machine), one machine:

1. starts at home and **scans outward** across zones, using the separators,
   to find `i₀ := zoneShiftIndex d (z t)`, the least level whose zone on the
   feeding side is non-empty. This is a new pure definition;
2. realizes the pure cascade at `i₀` on track `t` in a single
   outward-then-inward sweep, with mapped sweeps between adjacent zones and
   the scratch tape as the buffer;
3. leaves every other track and the separators unchanged, and returns home.

Its contract has the same shape as the current rows: exact final tape, live
exit or halt as the consumer needs, time `O(2^{i₀})`, the head within the
level-`(i₀+1)` extent, and scratch space `O(2^{i₀})`.

- **The left-move mirror** `zoneCascadeLeft` is new. It is defined through a
  pure left/right swap of `ZoneContents`, with its lemmas derived by
  symmetry, never copied.
- **The extent:** the carrier lays out `ℓ` levels, and a separate
  **extension row** lays out level `ℓ` (separator plus a half-full fresh
  zone, as in [AB09]'s "first time we encounter it") in `O(2^ℓ)`
  (decision 13d.2).

**G5. The assembly (stage-1 consumer, sketched for fit, not part of this
layer).** One simulated step:

1. read the home tuple;
2. apply M's transition in finite control;
3. write the home tuple;
4. rebalance each track by its head's move: `k` calls of G4, plus extension
   when needed;
5. handle the input and output tapes directly.

The amortization `Σ_i T/2^{i-1} · 2^i = O(T log T)` is the consumer's
mathematics, as before. Then `alphabet_reduction` turns the two-tape
`ZoneSym k` machine into a two-tape binary machine. With the Z3 two-tape
codes and the two-tape universal machine, Thm 3.1 follows at `f log f`.

#### What stays and what goes

- **Kept unchanged:**
  - the pure zone layer in `Build/Zone.lean` (about 820 of its 1,191
    lines): layout arithmetic, carrier, represented word, pairwise ops, head
    steps, the cascade and its lemmas, and the cardinality export. Its
    statements are untouched;
  - the rest of §13: Z1, Z3, Z5;
  - §12.6 and §12.7.

  No other file imports `Zone.lean`.
- **Superseded, to be retired through the G3/G4 gate:**
  - the binary physical realization `zoneTape`, `zoneTape_empty`,
    `zoneTape_blank_outside` and `zoneTape_homeWrite`;
  - the paired-cell codec, unneeded with a rich alphabet;
  - ZF-A2's seven staging-window lemmas;
  - the two current row statements, `exists_zoneShiftInTM` and
    `exists_zoneShiftOutTM`, to be replaced by the G4 rows.
- **ZF-A3's checkpoint** is held, not integrated. Almost all of it (counter
  navigation, counter construction, the binary window readout) becomes
  unnecessary. Integrate nothing from it unless G4's design reuses a piece.

#### Sequencing (each Lean step a PR plus its own gate, per the rule above)

1. **G1:** the generalization as one batch, its statements verified as
   instances, with the full downstream replay; then a **G1 audit gate**.
2. **G2–G4 statements:** the mapped sweeps, the carrier, the rebalance and
   extension rows, the swap mirror and the index function, with an executed
   pre-ship check on concrete instances; then a **statement gate**.
3. **Fill batches** for G2 and G4, then a **fill gate**.
4. The stage-1 Hennie–Stearns assembly, which needs its own statement
   phase.

#### Open decisions (13d.x, for the user)

1. **Zone boundaries:** blank separator cells (proposed; they give the
   catalog delimiters and boundaries at once) or a boundary flag in `Γ`
   (needs predicate-stopping sweeps instead).
2. **The extent:** a laid-out `ℓ` plus an extension row (proposed), or
   rows that extend lazily themselves.
3. **Rebalance totality:** realize the total pure cascade at the scanned
   index for every input (proposed; the A-S2 totality lesson, and the pure
   ops are already total), or a contract conditional on the classical
   fullness invariant.
4. **The track index:** in finite control, one row instance per
   `(direction, track)` (proposed), or on a tape.
5. **The shape of `Γ`:** `Bool ⊕ ZoneCell k` (proposed) or a structure
   with a bit field.
6. **Retiring the superseded declarations:** delete them through the G3/G4
   gate (proposed, since nothing imports them), or deprecate them first.
7. **G1's extent:** whether `Build/Loop.lean`'s public hosts also
   generalize now, or only when a large-alphabet consumer needs them.
   Proposed: only Seam, Embed, `bufferTape` and the R3 sweeps now.

#### Decisions 13d.1–13d.7 taken (user, 2026-10-10): all as proposed

1. Zone boundaries are **blank separator cells**.
2. **A laid-out `ℓ` plus an extension row.**
3. **Total rebalance contracts**: the rows realize the total pure cascade at
   the scanned index for every input.
4. **The track index lives in finite control.**
5. **`ZoneSym k := Bool ⊕ ZoneCell k`.**
6. The superseded declarations are **deleted through the G3/G4 gate**.
7. **G1 covers only Seam, Embed, `bufferTape` and the R3 sweeps.** What this
   means for the sweeps: the *definitions* of `transferTM`, `copyTM`,
   `clearTM` and `compareTM` (the last needs `[DecidableEq Symbol]`), and the
   three framed sweep contracts `transferTM_run_ofCfg`, `copyTM_run_ofCfg`
   and `clearTM_run_ofCfg`, generalize. The canonical `Cfg.ofWords` rows,
   the space rows, the compare contracts, and everything about `incrementTM`
   stay Bool-specific. The generalized definitions instantiate at `Bool`.

The G1 brief is `campaign/fills/s13d/briefs/s13d-g1-generalize.md`.

**Scope (user, 2026-10-12; §16b item 5).** G2–G4 and the Hennie–Stearns assembly stay in this
campaign. They follow MIG-0b, so that their rows are stated as `Contract`s from the start.

## 14. Hosts first: the rule and the host registry (user, 2026-10-12)

**The rule** (`policy.md` §1, **Hosts come first**; `workflow.md` §2 and §4,
ground rule 4). A *host* is a control structure that drives other routines:
a search or traversal, a recursion or evaluation scheme, an interpreter step
block, a clocked or windowed runner, a dispatcher over a data structure, or an
input device. A host is never built `private` inside the proof that first
needs it. Its public contract is designed and statement-gated first, generic
in what its consumers vary, with time and head-envelope clauses; consumers
cite it, proved modulo while its fill runs. Leaf rows (copy, compare, seek,
arithmetic) are not hosts and keep the §4 rule of admission.

**Why** (the library-reuse assessment of 2026-10-12, four read-only reviews of
the tip `3462c1b4`). The configuration-level calculus (§12–§13: framed sweeps,
`scanTM`, seams, the phase host, R1 embedding, symbol lifts, counter loops,
configuration records) is general: alphabet-generic, with exact time, framing
and head envelopes. Overfitting entered one level up, where every theorem got
its own private host, because the briefs' ground rule 1 made new helpers
private by default:
- NP ⊆ PSPACE's evaluation host (`SpaceComplexity/Inclusions.lean`, about 70
  privates), S1b's BFS and windowed pieces (private by `campaign/fills/ch34/briefs/ch34-s1b.md`,
  which lists three promotion candidates), B4 membership's assignment walker
  (private by `campaign/fills/ch34/briefs/ch34-b4-mem.md`), and Cook–Levin's machine-to-formula
  kit (private in `CookLevin/Hardness.lean`);
- four configuration encodings (`coreCode`, `cfgRecord`, B4a's bit rows,
  Cook–Levin's snapshot blocks) and three reachability notions (configuration
  reachability in `ConfigGraph`, `Complexity.GraphReach`, `Kruskal.Reach`),
  none linked to Mathlib's `Digraph`/`SimpleGraph`;
- about 300 `f2_` private copies in `Build/Catalog.lean`, there only to attach
  space bounds to rows exported as existentials (the §2 design rule, *named*
  machines with spec theorems, was not followed by those rows).

**The registry.** Status as of 2026-10-12. Rows H7–H13, and the reconciliations of H1, H3, H4
and H6, were added 2026-10-14 (the ARM fill gate, finding 5). Row H14 was added 2026-11-05
(gate 03l, ruling R-03l-1). Each entry gets a public contract
and a statement gate before a second consumer is briefed.

| # | Host | Status | Named consumers |
|---|---|---|---|
| 0 | **Framed-contract structure**: machine, entry/exit states, precondition, endpoint as a function of the start configuration, time, no-earlier-exit cut, head envelope; sequencing, phase host, R1 embedding, lift and counter loop as structure-to-structure theorems, space derived | to design; **requirements revised by §16** (exact time and cut first-class) | every host below; removes the inline restatements of the delimited-word precondition |
| H1 | **AND/OR evaluator**: a depth-first odometer over a path word of per-depth records with node kinds (AND/OR), a pluggable leaf-verdict module with its own framed contract, short-circuit semantics as a pure function; space = path + leaf + O(1) | **reconciled 2026-10-14:** the machine form exists, received: `LogProg.TQBFARM` (H13e) proves `TQBF_mem_PSPACE` by a depth-first walk with the assignment as a stack register (accepted exception). The private pure core in `TQBF.lean`'s `b4m*` appendix is dead and is deleted by the payback PR (D6); MIG-22 is moot. The general AND/OR evaluator remains to be designed; its contract gate decides between this machine and §15's language. *(Was: the pure core private in B4 membership's partial; language first, user 2026-10-12.)* | `TQBF_mem_PSPACE` (served by H13e); Savitch (served by H13a for polynomial `S`; midpoint records as digits); NP ⊆ PSPACE (re-derivation); `ClassPSPACE/Games.lean`'s game values; backtracking in the §15 layer |
| H2 | **Step block**: one simulated transition of a `k`-tape coded table, relation-level, with per-round time `B·(\|table\| + 1)` and a head envelope | **the complete step block is proved, private, in B5a H1's continuation (fills-7):** `h1RoundTM k`, one finite machine per `k` whose control does not depend on the state count, with `h1Round_effect` (`0 < T ≤ 50·(\|table\| + 1)`, strict interior, silent, head envelope). **Promoted (2026-10-14, H2-M, PR #88):** public in `Build/StepBlock.lean` as `Turing.StepBlock.roundTM`, with `roundTM_effect`, under the round-2 names (backlog F7-1(a)). **H2-L, its loop form, landed (2026-10-14, PR #94):** `Build/StepBlockLoop.lean`, `Turing.StepBlock.loopTM`/`hostedLoopTM` with `loopTM_run`, `hostedLoopTM_run`, `hostedLoop_read` (H1 harvest gate, CLOSED). **H2-F, its forwarding (unclocked) loop form (2026-10-15; U2 statement gate CLOSED, PASS 0/0/2; PR #102):** `Build/StepBlockForward.lean`, `Turing.StepBlock.forwardLoopCfg` (defined) and `Turing.StepBlock.exists_forwardLoopTM` (**proved**, 2026-10-16, the H2-F fill, landed by PR #114: the round block released into a phase host with a forwarding leaf, per-step cost `T + 3` live and `T + 2` at a halt, `C = 3`): a macro-step `Turing.Lockstep` of any `k`-tape table through `forwardLoopCfg`, emissions forwarded, per-step cost `0 < cost ≤ 50·(\|tableBitsK\| + 1) + C`, and a per-head space ledger (mirrored heads within the source's visited cells, the two auxiliary heads within that bound); its own module so that the clocked form's consumers (`CodeSimulator`) do not depend on it (user, 2026-10-15) | H1 (`exists_uniformSimulator`); U-1; B6's self-application universal; H2-F: U2-U (`exists_selfUniversalK`), U2-E (`universalK`), B6's `U₀` at `k = 1`, U-1; C1 (unchanged, at `k = 3`, through the replay machine `NDTM.replayTM`); EXPCOM |
| H3 | **Windowed runner**: run a fixed machine on a windowed record, exiting on window exit, simulated halt, or a configuration-count clock | parts exist privately in S1b's partial (radius phase, records-to-runs bridge, the general-`S` count). S1b stopped (fills-6); B6's window route is the next consumer (adopted, §16b item 3). **B6's hosts landed (PR #92, 2026-10-14):** `Build/WindowRun` and `SpaceComplexity/WindowClock` state its public contracts, sorried for B6's fills. S1b's remaining private block is dead, and the payback PR deletes it. See H9 for the received configuration count | B6 (the window route; gated, `campaign/gates/13-b6-hosts-statements/findings.md`); Savitch and NL = coNL (served by H13a and H13b); S1b (stopped) |
| H4 | **Search over a graph presented by rows** (enumerate, equality, adjacency, start, target), visited table, BFS | **reconciled 2026-10-14:** built at ARM level for `NSPACE ⊆ DTIME(2^O(S))` (H12, received, accepted exception); MIG-19 is moot. The general search over row-presented graphs remains to be designed (H10's code languages are a row presentation). *(Was: not built; language first, MIG-19.)* | `NL ⊆ P` and `NSPACE ⊆ DTIME(2^O(S))` (served by H12); Immerman–Szelepcsényi counting (served by H13b); `PATH ∈ P`; §15 graph algorithms |
| H5 | **Input devices** behind one interface: native, buffered (Z1, exists), unary marker, binary position (from `exists_inputSeekTM`), computed input | partial | B6 / `space_universal`; U-1 and H2 (backlog); C1 |
| H6 | **Machine-to-formula kit**: closed-form variable indexing, snapshot-keyed local gates, ordered emission by `exists_emitLoopTM`, Tseitin on `Std.Sat.CNF ℕ` correct for every prefix assignment | pattern private in `CookLevin/Hardness.lean`; B4a's codec is non-uniform (its orderings range over index types depending on `n` and `s`, and its public statement is `∀ n s, ∃ …`). **B4a is restated in place over this kit's indexing** (user, 2026-10-12; §16b item 2) | TQBF hardness (served instead by H13f's route: the uniform tableau, Tseitin after the prefix); Cook–Levin deduplication; later machine-to-formula reductions. B4a's restatement (§16b item 2) has no consumer while RD-2's fills are held |
| H7 | **ARM compiler and its decision bridges** (Hydroxyi's `LogProg` tree, `SpaceComplexity/Machines/`): the register-tape compiler from an arbitrary seam (`compile_correct_from`), the space bridge `arm_space`, and the decision bridges at logarithmic width (`arm_decides`, `arm_decides_poly`) and at general width (`arm_decides_space`, `arm_decides_SPACE`, `arm_decides_pspace`, `_of_logspace`, `_val`); the loop and reachability kit (`GuardLe`, `ARMLoops`, `arm_reach`, `VWord`) | **received 2026-10-14 (`8c23f3bc`); public, ungated; first uses an accepted exception (decision 3).** `compile_correct_from` and the wide bridges are new; `arm_decides`, `arm_space` predate (chapter-6 campaign, `f70c57c2`). No time clause: ARM instructions are unary in register values, so time goes through H9 | `TQBF_mem_PSPACE` (H13e), `PSPACE_eq_NPSPACE` (H13a), the codec's deciders (H10), the PATH-hardness bit deciders (H13d), `searchLang_mem_PSPACE` (example); through H8/H9 every ND and time customer |
| H8 | **Nondeterministic ARM (NARM)**: `choose` instructions driven by a choice word, compiled to a `FinNDTM` by the `detPart` override; the space bridge `narm_space` and the class bridges `narm_decides_space`, `narm_decides`, `narm_decides_poly`, `narm_decides_npspace`; the termination layer `NTerm`/`NAcc`/`NSem` | **received 2026-10-14; public, ungated; accepted exception.** Supersedes for now §16b item 4's route (C2 as programs with coins; stage 2 paused). Its all-branch budget is per input: uniform over one input's branches, not over input lengths | `PATH_mem_NL` (H13c), `compl_mem_NSPACE` and through it `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq` (H13b) |
| H9 | **Memory ARM (MARM) and its time bridge**: a monotone Boolean memory tape (`mread`, `mset`, `mleft`, `mright`), compiled by the same `detPart` override; the configuration count `runFrom_count_eq` and the bridge `marm_dtime` into `DTIME` | **received 2026-10-14; public, ungated; accepted exception.** The count needs the monotone-write hypothesis `hwrite` and is valid along one run only | `NSPACE_subset_exp_dtime` (H12), hence `NL_subset_P`, `polyTimeReducible_of_mem_NL` |
| H10 | **Configuration codec and code deciders** (the fifth configuration encoding): `cfgWord`/`cfgCode` over the shared window `Turing.Cfg.InWindow` (`TuringMachine/Build/CfgRecord.lean`), the bound `cfgCode_lt`, injectivity up to `NDTM.coreSum`, the decoder; the four code languages and their `LOGSPACE` deciders; the chain bridge `mem_iff_codeChain` / `mem_of_codePath` | **received 2026-10-14; public, ungated; accepted exception.** The codec's own window predicate `InWin` was retired into `Turing.Cfg.InWindow` by the payback (D1; PR #101, landed 2026-10-15; its 28 restatements gated post-merge by the ARM gate's round 3). RD-2's `ConfigCodec` has no consumer (fills held) | H13a (Savitch), H13b (inductive counting, through H13a's decider bank), H13d (PATH hardness), H12 (`ExpBFS`), H13f (TQBF hardness's verifier and machine) |
| H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index (their answers `indicator_inputBitLang`/`indicator_inputLenLang`), the stride decoder `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance), the increment/decrement chain `arm_chain`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` were done in the payback (PR #101, landed 2026-10-15): `Codec/Engine`'s `decodeStride_loop` and `incChain`/`decChain` are instances of `boundedDecodeStride_loop` and `arm_chain` | every received ARM customer through its decider bank; `Codec/Engine` (its decoder and chains are instances); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
| H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius` directly, `ISCountGenCorrect` transitively) |
| H13 | **The customer machines**, each with its named consumers and its own reachability notion: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |
| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`); head envelopes `Clean.envelope` (a clean module's heads stay within `B \|arg\|` cells of the origin at every time), `host_call_envelope` (within `t` cells up to time `t` of a call) and `host_clean_envelope` (`host_clean` with the envelope `B \|arg\|` throughout the call), the coarse envelopes from the time bounds and the unit head moves of `Turing.MultiTapeTM.workTapePos_step_le` | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round; head-envelope clauses added 2026-11-06 (gate 03l round 2, finding 1).** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |

**The received ARM machinery, H7–H13** (registered 2026-10-14: the ARM fill gate's round 2,
finding 5; user decision 3). The rows' public contracts, with file and line, are in
`campaign/fills/arm/evidence/arm-fill/r2/registry-rows.md`. Its lines are at `e831b5b0`, with one correction:
`vword_whole₁` is at `Logspace/InputAccess.lean:93`, not 90.
- **Accepted exception.** Their first uses, the consumers named above, all inside the delivery
  `8c23f3bc`, are an accepted exception to *hosts come first*: they were not statement-gated
  before their consumers were written.
- **Gate before reuse.** No further consumer of H7–H13 is briefed until that row's public contract
  has passed a contract gate, of the contract as listed or of its generic form.
- **Named consumers** are direct importers and named transitive users, marked as such.
- **Generic forms** are ARM-2's direction (backlog §1 ARM-2), designed with Hydroxyi.

**C1's hosts (landed 2026-10-14, PR #87; gate `campaign/gates/12-c1-hosts-statements/findings.md`).** The
nondeterministic phase host `NDTM.phaseHostND` (`Build/NDHost`), the choice writer `ndWriterTM`
(an H5 device), the window copier `exists_inputWindowCopyTM` (`Build/InputWindow`), the
interpreter core `R` = `exists_ndInterpreterCore` (`NDCodeSimulator`) and the exhaustive decider
`E` = `FinNDTM.exists_exhaustiveDecider` (`ClassNP/ExhaustiveReplay`); their contracts are
sorried for the C1 fills.

Pure-Lean kits that the hosts' semantics share (not machines, so not hosts,
but designed with them): bounded reachability (`ReachWithin`, the midpoint
lemma, pigeonhole shortening) with bridges from configuration reachability,
`GraphReach` and `Kruskal.Reach` to Mathlib's `Digraph`/`SimpleGraph`.
Consumers: Savitch, TQBF hardness, Immerman–Szelepcsényi, PATH, §15. The received code added
four more reachability notions, each with its own consumer: `WalkLe`, `SavitchARM.Reach`,
`ExpBFS.RCode` and `TQBFHard.Mid`/`mid_iff_steps`. The bounded-reachability kit, when designed,
bridges them (2026-10-14).

**Work in flight when the rule was adopted.** No in-flight brief is withdrawn.
B4 membership and B5a H1 received addenda (`campaign/fills/ch34/briefs/ch34-b4-mem-addendum-1.md`,
`campaign/fills/b5a/briefs/b5a-fill-h1-addendum-1.md`): their hosts stay private for now, as
their ownership requires, but are written generic, with self-contained
statements, and listed as promotion candidates. They and S1b's candidates are
promoted, by PR and gate, before any second consumer is briefed.

**Proposed sequencing** (maintainer; for the user): item 0, then H1 (two
consumers ready: TQBF membership and Savitch), then H3/H4 from S1b's delivery,
then H5 with H2's self-application universal for B6, then H6 for TQBF
hardness. Each is a statement phase plus its gate, then a fill.

## 15. The programming layer (commissioned by the user, 2026-10-12)

**Decision.** "Support a programming layer now, now that we've got the really
low level stuff working" (user, 2026-10-12). This supersedes §1's non-goal.

**Why now.** The routine layer (§12), framed contracts (§12.6), counter loops
(§12.7), configuration records and tables (§12.8, §12.8b) and the zone and
virtual-input layer (§13) are proved or being filled. What is missing is any
way to write an algorithm once and get a machine with a proved bound:
- `CounterProg` has unary registers, `inc`/`dec`/`jz`/`out`/`pr` and a one-way
  input, compiled with a `t(2t + 3)` overhead (`CounterProgRun.lean`). It
  serves emitters, but cannot hold a string, an array or a graph;
- `LogProg.ARM` has `O(log n)`-bit registers and yes/no answers, and compiles
  for space only;
- the `PolyTimeComputable` closure algebra is `Bool`-only and existential;
- none of the three is built on `Build/`, and none is registered in
  `ComputationalModels.lean`.

So every machine-level algorithm is a hand-built host (§14), and an
introductory algorithms curriculum (graph search, shortest paths, MST,
sorting, with running times) cannot be written at all. The only
cost-annotated code, the `TimeM` in `Cryptography/RSA.lean`, charges trusted,
unchecked costs.

**Goals.** Write an algorithm once, as a program, and obtain: its semantics;
a step count that is sound by construction (only primitives charge cost);
and a compiled `FinTM` with a proved time bound polynomial in the program's
cost and a space bound linear in its register footprint, feeding `∈ P`,
`PolyTimeComputable` and `SPACE` memberships. The compile theorem is proved
once, from the contracts of the rows and hosts, never by tracing runs.

**Proposed architecture** (maintainer draft; decisions 15.x below):

```
L4  Algorithms     TCSlib/Algorithms/: curriculum algorithms, specs against Mathlib
L3  Programs       a deep-embedded structured language over word registers (+ arrays),
                   big-step semantics with cost, compile theorem to FinTM
L2  Contracts      the framed-contract structure (§14 item 0) and the registered hosts
L1  Routines       Build/: catalog rows, scans, seams, loops, records, tables
L0  Model          MultiTapeTM / FinTM, the run calculus
```

- **L3, programs.** Registers hold words over a finite alphabet, one tape
  each. Instructions are the catalog's word operations (copy, clear, append,
  compare, binary increment, add and `≤`, seek within delimited fields), reads
  of the native input, clean calls of `ComputesFunInTime` machines on
  registers, structured control (sequence, `if` on a register test, a bounded
  `for` over a register's value by counter loops, `while` with fuel), and
  calls of registered hosts. Each instruction is charged by its row's cost in
  the register lengths. Arrays and maps, in a later increment, are record
  tables (§12.8b) with charged access.
- **L4, algorithms.** Written in L3 when machine-faithful costs are the point,
  or as functional code over a cost model that is sound by construction (a
  query or operation monad whose primitives are the only cost source), with
  specifications against Mathlib (`List.Sorted`, `List.Perm`,
  `SimpleGraph.Reachable`, `Digraph`). The comparison-query form also states
  the sorting lower bound. `RSA.lean`'s `TimeM` (colleague-owned) is a
  candidate to relocate or replace here, after a provenance check
  (`backlog.md` §5).
- **Existing layers.** `CounterProg` and `LogProg.ARM` stay; each is bridged to
  L3 or re-based on it (15.4). The new models are registered in
  `ComputationalModels.lean` (policy §1, model registry).

**Open decisions (15.x, for the user).**
1. **Embedding.** (a) A deep embedding: syntax, semantics and a verified
   compiler (cost-sound by construction, the most reusable, the largest); or
   (b) shallow: programs are compositions of §14's contract structures
   (cheaper, but no syntax to reason about or teach from). Maintainer lean:
   (a), compiling into (b).
2. **Register alphabet.** `Bool` only, or any finite alphabet with
   `alphabet_reduction` at the end.
3. **First memory model.** Registers only, or registers plus record-table
   arrays from the start.
4. **`CounterProg` and `LogProg.ARM`.** Bridge, re-base, or leave as they are.
5. **Curriculum cost model.** A comparison-query monad first (sorting), an
   operation monad (graphs), or curriculum algorithms written in L3 directly.
6. **Shape of the compile bound.** Per-instruction affine in the register
   lengths (`C·(cost + n + 1)` overall, with register lengths bounded by the
   cost), or a polynomial.
7. **First consumers** (rule of admission, §4: two named customers). Proposed:
   machine side, the `NL ⊆ P` BFS (or `PATH ∈ P`) and TQBF membership or
   Savitch; curriculum side, merge sort and BFS.

**Prior art examined (2026-10-12; nothing taken yet).** Two formalizations of the
same result, Alman and Vassilevska Williams, *Truly Subquadratic 3SUM and Truly
Subcubic APSP via Triangles in Sparse Lopsided Graphs* (arXiv:2610.06783v1). Both
are word-RAM developments with a structured language, a program logic and a
verified compiler:
- **[AFM26]**: `anthropics/formal-math`, folder `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0, © Anthropic,
  PBC, on Lean and Mathlib v4.33.1. It has 434 Lean files and 102,310 lines. Its parts:
  - the trusted `EndStatement.lean` (139 lines, core Lean only);
  - the language, logic and compiler in `Lang/` (about 9,000 lines) and `Machine/`
    (about 840);
  - the paper's algorithms as verified programs in `Programs/` (about 52,600).
- **[Xuanji26]**: user **xuanji on prove2me** (citation as directed by the user),
  file `3sumapsp_example.lean`, examined locally. It is the top-level assembly of a
  stronger 3SUM bound, `O(n^1.999074)` against [AFM26]'s `O(n^1.9992)`, which comes
  from an Exact Triangle saving of `9261/5000000`. The file builds on [AFM26]'s
  library: 264 of its 265 module docstrings and 125 of its 128 theorem blocks are
  verbatim in [AFM26]. Its 62 project imports, including the module that proves the
  improved saving, are not in the file.

The designs that §14 and §15 may adapt from them are:
- the program logic (`Ends`, `Meets`: postcondition predicates, time "within `T`",
  handed on rather than added up, and spec-only calls);
- the `SameOn` framing with `.keep` lemmas and default-argument tactics;
- tasks, solvers and hosts (`IsHost`);
- run limits built into the semantics;
- the `DetTimeModel` claim algebra;
- the asymptotics calculus with its `growth` tactic.

If adapted, they are cited per `policy.md` §2, *Design adaptation*: [AFM26] as the
origin of the design, and [Xuanji26] for the file the user supplied.

**Sequencing.** 15a: the contract structure (shared with §14). 15b: L3 with
registers only, its semantics, cost and compile theorem (a statement phase and
its gate, then fills). 15c: arrays over record tables. 15d: the curriculum
layer's first increment (cost model, merge sort with `≤ n⌈log₂ n⌉`
comparisons, BFS with an `O(n + m)` operation count). Every Lean step is a PR
plus its own gate.

### 15a. Language first; the spike (user decision and maintainer draft, 2026-10-12)

**Decision (user, 2026-10-12): language first.** The remaining results that are
algorithms are written as programs of the §15 language and compiled. (§16, decision 3,
confirms this for Savitch and `NSPACE ⊆ DTIME(2^O(S))`, which need machine-configuration routines
in the language.) These are
Savitch's recursion, the AND/OR evaluator (H1), graph search (H4), and the
intro-algorithms curriculum. The hosts that are *about machines* stay at machine
level and proceed now: H2 (step block), H3 (windowed runner), H5 (input devices)
and H6 (machine-to-formula). Work in flight is unaffected. S1b's BFS and B4's
walker finish as briefed, and may later be re-derived as programs.

**Architecture (proposed): two stages, as in [AFM26].**

```
program of the language  --stage 1-->  flat word-RAM program  --stage 2-->  FinTM Bool
                        (compiler; constant          (one simulation; polynomial
                         overhead, no tapes)          overhead, the only tapes)
```

- **Stage 1** is pure program reasoning and never mentions tapes. [AFM26]'s
  compiler from its language to its word RAM is about 2,500 lines. Its theorem
  says a run of `c` steps becomes at most `startCost + stepsPerStep·c` RAM steps,
  with constants that depend only on the program text.
- **Stage 2** is the only place tapes appear: one machine simulates a fixed RAM
  program, one instruction at a time. The RAM has about a dozen instruction
  kinds, so the tape-level proof surface is about a dozen instruction contracts
  (§14 item 0), one dispatcher over the program counter (the phase host), and one
  simulation induction.
- **The word RAM is a model in its own right**, registered in
  `ComputationalModels.lean`. In it the curriculum's statements have faithful,
  constant-factor costs. Stage 2 then turns them into P, PSPACE and L
  memberships.

**The language.** It is [AFM26]'s light language:
- integers and numbered local variables, with a flat memory `ℕ → ℤ`;
- expressions: constants, `+`, `−`, `×` and loads; tests `<` and `=`;
- statements: skip, assignment, store, sequence, if, while, and procedure calls,
  with recursion;
- unit costs per constant, variable, operation and load;
- the limits `word`, `space` and `depth` as part of the semantics;
- the logic `Ends`/`Meets` with its rules, frames and tactics.

It adds three things that our classes need:
- `inBit e` and `inLen`, which read the input string *in place*, never copied
  (logspace needs this);
- `emit e`, which appends a bit to the output, for reductions and function
  problems;
- possibly `half e`, cheap on both targets (decision 15a.4).

**The RAM.** It is [AFM26]'s `EndStatement.Instr`:
- `one`, and `add`/`sub`/`mul` modulo `2^W`;
- `load` and `store` (indirect);
- `bltz`, `accept` and `reject`.

It adds `rdIn` (an input bit at a computed position), `len` and `emit`.

**Stage 2's theorem (statement shape, draft).** For a RAM program `P` there are a
`FinTM Bool` machine `M` and a constant `A` (depending on `P` only) with the
following property. Whenever `P` halts on input `x` with word size `W` within `t`
steps, touching `f` distinct cells:
- `M` halts on `x` with the same verdict and output within
  `A·(t + 1)·(f·(W + a) + W² + |x|·log|x| + 1)` steps, where `a` is the width of
  an address;
- `M`'s space is at most `A·(f·(W + a) + W + log|x| + 1)`.

The per-step cost is dominated by one scan of the memory table, a
shift-and-add multiplication, and one input seek.

**What consumers get.**
- **P:** polynomial cost and limits give membership in P.
- **L:** `O(1)` cells, bounded depth and `W = O(log n)` give space `O(log n)`,
  because the input is read in place.
- **Savitch:** depth `O(S)` with `O(1)` locals of `O(S)` bits gives `O(S²)`.
- **TQBF ∈ PSPACE:** depth `O(n)` with `W = O(log n)` gives `O(n log n)`.

Results that need tight *linear* space may still want direct machines.

**Reuse from `Build/`:**
- the phase host, for dispatch on the program counter;
- the framed copy, compare, clear and increment rows;
- the `scanTM` carry family, for binary addition;
- `exists_inputSeekTM` and `exists_inputLengthTM`;
- counter loops, for the rounds of a multiplication;
- R1 embedding and `alphabet_reduction`.

**New rows needed:**
- two-tape addition and subtraction modulo `2^W`;
- multiplication;
- a sign test;
- find-by-key in a memory table, where the key is a word on another tape. The
  record-table find takes a finite-state predicate, so it does not cover this;
- in-place overwrite of a fixed-width field.

**Rough cost** (maintainer estimate, in lines):
- item 0's contract structure: 1,500–2,000;
- stage 2: 6,000–10,000;
- stage 1 with the language, logic and tactics: 5,000–7,000 if ported from
  [AFM26], more if re-implemented.

That is about 15,000–20,000 lines in all, or a few fill waves: about the size of
S1b plus the record tables.

**Open decisions (15a.x, for the user):**
1. **Two stages** (recommended) or a direct compiler from the language to machines.
2. **Port or re-implement [AFM26]'s language, logic and compiler.**
   - *Port:* Apache-2.0, vendored with its header, the upstream commit and a list
     of local modifications (`policy.md` §2, *Vendored code*).
   - *Re-implement:* follow the design, with a *Design adaptation* citation.

   A port is not mechanical. [AFM26] uses Lean v4.33's module system (`module`,
   `public import`, `@[expose] public section`), which our pin v4.25.0 and its
   Mathlib do not use. Porting means removing that layer and repairing
   Mathlib API drift. A port trial on the core (syntax, logic, rules, frames,
   calls, tactics and regions, about 1,900 lines) would settle it.
3. **The RAM's input convention:** read in place by instruction (recommended;
   logspace needs it), or loaded into memory as in [AFM26] (kept as a variant
   for curriculum statements).
4. **Halving** (`half e`) in the language and the RAM: yes or no.

**Next step after 15a.1–15a.3.** Statement drafts of item 0's contract structure
and of stage 2's theorem, as sorried Lean in a scratch worktree, with a pre-ship
elaboration check. Then a statement gate.

### 15b. The port of [AFM26]'s language, logic, routines and compiler (user decision, 2026-10-12)

**Decision (user, 2026-10-12): port it.** The user asked two things first:
- *Does their core serve our purposes?* It serves all of the language-first list, which is
  deterministic. Nondeterminism and randomization are not covered and become one planned
  extension, the coin stream (below).
- *Does their licence allow it?* Yes: Apache-2.0, as tcslib is. Vendored files keep their headers,
  list their changes, and carry the upstream `NOTICE` (repository `NOTICE`).

**The trial port**, read-only, with no build products:
- **Core and routines.** The language core with the merge-sort and power-table closures (18
  modules, 3,681 lines) elaborated at our v4.25.0 pin with 0 errors.
- **Compiler.** The compiler's correctness closure (23 modules, 5,565 lines) also elaborated with
  0 errors.
- **Axioms.** `sort_meets`, `merge_meets`, `powTable_meets`, `time_split`,
  `compileProgram_correct` and `sim` depend only on `[propext, Classical.choice, Quot.sound]`.

**What is vendored.** `TCSlib/Programs/` holds 41 modules (8,548 lines of the trial set) plus
`Compat.lean` and the facades `Programs`, `Programs/Util`, `Programs/WordRAM` and
`Programs/Light`:
- the language, its logic and tactics (`Light/`);
- 14 verified routines (`Light/Lib/`): copy, fill, merge, merge sort, counting sort, radix
  pass, logarithms, powers, modular reduction, square root, odometer and others;
- the compiler to the word RAM (`Light/Compiler/`, with `compileProgram_correct`);
- the word RAM and its run facts (`WordRAM/`);
- general list and index facts (`Util/`).

Their sieve is deferred: it needs `Nat.primesLE`, which our Mathlib pin lacks. The port is the
41-module import closure of the roots named in `scripts/vendor_afm26/README.md`. Two generic
upstream modules outside that closure are **deferred**, not excluded on principle (fidelity
gate, finding 3):
- `Lang/Renumber.lean` (procedure relocation), a candidate for the compiler extensions;
- `Machine/Footprint.lean` (read/write footprints), a candidate input to stage 2's space bound. The files are
generated by `scripts/vendor_afm26/` from upstream plus a recorded list of changes. The
per-file diff is `campaign/gates/programs-vendor/evidence/upstream-to-vendored.diff`, and the file map is
`.../file-map.md`.

**Local modifications** (listed in each file's header):
- the Lean module-system syntax removed, as in the cslib precedent;
- namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp`
  to `Light`;
- `EndStatement.lean` trimmed to the word RAM;
- `## References` sections and the standard options added;
- `with_unfolding_none`, absent in v4.25, replaced by `with_reducible`. This is an approximation:
  it keeps reducible definitions unfoldable, and every vendored proof passes with it;
- nine v4.25 proof repairs (`scripts/vendor_afm26/fixes.py`). Seven insert a beta reduction,
  because v4.25 leaves an instantiated motive or invariant unreduced. One rewrites a cast step,
  and one completes a `split_ifs`;
- three renamed lemmas provided in `Compat.lean`, each to be removed at the Mathlib bump that
  provides it.

**Checks.**
- The shipped files, concatenated, elaborate with 0 errors together with all fifteen
  `Complexity` facades and `ComputationalModels`. They declare 2,990 constants, none of which uses
  `sorryAx`, and no axiom.
- A textual screen of the 713 new public names against the other areas finds no clash.
- The style lint reports 0 FAIL and 0 WARN over the 45 files. The vendored files are registered
  as such.
- The user-run replay compiles each module separately, in dependency order
  (`campaign/gates/programs-vendor/evidence/replay-order.txt`). Its first run found one import gap.
  `Util/Index` uses a Batteries lemma that upstream reaches through its imports at Mathlib v4.33
  and ours does not; 16 modules failed with it. The fix is an added
  `import Batteries.Data.Nat.Lemmas`, listed in the file's header.
- The concatenated check had masked that gap: its union of all files' imports contained the
  lemma. A per-module closure check now elaborates each of the 46 modules and facades in exactly
  its own import environment (`scripts/vendor_afm26/closurecheck.py`), and all 46 are clean
  (`campaign/gates/programs-vendor/logs/programs-vendor-closure-check.log`).
- **Replay passed** (user-run, at `155255ed`; `campaign/gates/programs-vendor/logs/programs-vendor-replay.log`). All 47
  entries are clean, with 0 errors and no `sorry` warnings: the 42 modules, the four facades and
  `ComputationalModels`. The resumed run rebuilt the 17 modules that had failed and skipped the 30
  that were already clean.

**Models registered** in `ComputationalModels.lean`: `Light.Program` and `WordRAM.Instr`.

**Next, each a statement phase with its gate:**
1. the extensions: reading the input in place (`inBit`, `inLen`), `emit`, and the coin stream
   (`coin x`, read for each fixed stream, so that the deterministic logic and compiler carry
   over; nondeterminism and randomization then quantify over the stream);
2. stage 2, the RAM-to-`FinTM` simulation, with the contract structure (§14 item 0);
3. the first consumers.

### 15c. The language and RAM extensions: semantics decided (user, 2026-10-12)

A read-only survey of the vendored layer (2026-10-12) costed the four extensions and their
options. **Decision (user): all four go into one scripted vendored edit set**, with the
survey's recommended semantics:

- **Input read in place.** A statement `x := inBit e` (cost `e.cost + 1`; past the end it reads
  `0`) and a RAM instruction `rdIn`. `inLen` comes first from an argument cell (`|x|` passed as
  argument `i`, which needs no change); a `len` instruction follows only if a consumer needs it.
  Statements rather than expressions, because expression code must be `Straight` and `effect`
  touches only memory. The input string goes into `Limits` (never constructed in the port,
  so nothing breaks), and `Fits` gains `|x| ≤ word`. Stage 2 maps `rdIn` to
  `exists_inputSeekTM`, and `load` stays a table lookup. The rejected options were mapping the
  input into memory at the RAM level, and keeping [AFM26]'s memory-loaded input, which forces
  `lim.space ≥ n` and so rules out logspace.
- **Where the I/O state lives: new indices of `Exec`.** The bits emitted (`o`) and the coins
  consumed (`r`) become indices of the big-step relation, concatenated by `seq` and `while` and
  passed through `call`. `Ends` keeps its type, hiding them under `∃`, so `Meets` and the 14
  routines are untouched; a new `EndsIO` lets a postcondition see them. Six files mention
  `Exec`, against about 124 state literals in 24 files had the state grown instead.
- **Coins read once**, as a consumed `List Bool`. `coin x` sets `x` to either bit at cost `1`,
  consuming it. For a fixed stream `ρ`, `EndsIO ρ` asks for a run whose consumed word is a prefix
  of `ρ`. Nondeterministic acceptance is "some `ρ` of length `T` accepts". Randomized
  acceptance uses `randProb` over `Fin m → Bool`, which needs a determinism lemma for `Exec`
  (not yet stated). **Time bounds are uniform over all streams**, as `NTIME` and `NSPACE`
  require. Read-once coins are also right for NL and BPL, where two-way access to the coins
  would give NP's power, and they compile to both kinds of target. Stage 2 makes each `coin` one
  NDTM choice step; for BPP it produces a deterministic machine that takes the coins as a second
  input.
- **`emit e`** appends a bit to an append-only output, mirroring the machines' per-step output.
  Strictly, only space-bounded output (log-space reductions) needs it; time-bounded functions
  can use memory output. It is included now because it changes the same signatures.
- **`half e`**, as a statement and a RAM arithmetic-shift instruction (not an `Op`: `Op` is
  binary, and its effect lemma needs a range hypothesis). It is `O(W)` in stage 2 and helps
  configurations packed into words.

**Estimated size:** 600–1,000 lines of vendored edits, made by the generator scripts in
`scripts/vendor_afm26/` and listed in each file's header, plus 700–1,150 new lines (the `EndsIO`
rules and tactics, acceptance and probability, the determinism lemma, the new `sim_*` cases).
Every new construct needs a case in each exhaustive definition and induction over `Stmt`,
`Exec` and `Instr`. The hardest parts are carrying the output and the coins through the compiler
simulation, and threading the input through the RAM's run calculus.

**Obstacles the survey found** (backlog PROG-2, PROG-3):
1. **No footprint along a run.** `compileProgram_correct` and `Finished` describe only the final
   memory. Stage 2's space bound needs every intermediate memory inside `[-lowCell, lim.space)`.
   That needs a stronger `Steps`, or the deferred `Footprint.lean` (PROG-1(e)). L and Savitch
   need it, whatever the extensions.
2. **`Ends` is existential.** With a nondeterministic coin rule, specifications that mention I/O
   need `EndsIO` with an explicit stream, and probabilities need the determinism lemma.
3. **`Fits` has no input-length clause** (above).

**Corrections to §15a and §15b, from the survey:**
- the RAM has nine instruction kinds, not "about a dozen";
- the RAM additions are `rdIn` (with `len` later), `emit`, `coin` and `half`;
- the deterministic logic and compiler do not carry over unchanged for coins: the stream
  position is state, carried here by `Exec`'s index;
- [AFM26]'s memory-loaded input is not in force in the port: `SolvedBy` was dropped, `loadWords`
  is unused, and the compile theorem takes any memory satisfying `Input`;
- logspace from `O(1)` cells holds only with input read in place, and only once obstacle 1 is
  closed.

### 15d. Stage 2, PROG-2 and PROG-3: statement drafts (2026-10-12)

A maintainer sub-agent drafted the statements, and the maintainer re-elaborated them: 0 errors;
the only warnings are `sorry`s. They are evidence, not landed files:
`campaign/items/stage2/Stage2Draft.lean.txt` (723 lines),
`campaign/items/stage2/ExtensionsDraft.lean.txt` (415 lines), and the notes
`campaign/items/stage2/NOTES.md`.

**Stage 2 (PROG-4).** It is drafted in two forms:
- `exists_simulation`, deterministic;
- `exists_ndSimulation`: each `coin` is one `FinNDTM` choice step, with bounds uniform over all
  coin streams.

Both are stated over a draft RAM that wraps the vendored one: the nine vendored instructions, plus
`rdIn`, `emit`, `coin` and `half`. With `n = |x|` and `W = W n`, the bounds are
`T = TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` and
`S = SW n + A·(f·(W + 1) + W + logSpace n + 1)`.
- **The word size** is a hypothesis `WordSizeComputable W TW SW`: some machine outputs
  `Nat.bits (W n)` within `TW n` steps and `SW n` cells. Two bridges supply it: `c·logSpace`,
  from the input-length counter R8.5c, and `c·S`, from `SpaceConstructible`.
- **The corollaries:** DTIME and P, SPACE and LOGSPACE, log-space transducers, Savitch's
  `SPACE(S·S)`, NSPACE and NL.

**PROG-3.** `compileProgram_footprint`: a compiled run stays inside `[-lowCell, lim.space)`, its
reads included. The gap is only at the RAM level, where `Steps` and `Finished` speak of the final
memory.

**PROG-2.** A self-contained mirror of the four new statements and of `Exec`, with the output word
and the consumed coins as indices; `EndsIO` with 15 rules; the determinism lemma; acceptance and
`acceptProb`. `NOTES.md` §5 lists, by file and line, every exhaustive definition and induction
the real edit must extend.

**Corrections to §15a and §15c, read off the code:**
- there is no separate address width, because addresses are words (`WordRAM/Basic.lean`);
- the input seek row is linear (`exists_inputSeekTM`), so the per-step seek term is `n`, not
  `n·log n`;
- the word size's own computation is charged once, as `TW` and `SW`;
- `inBit` needs no input-length clause in `Fits`;
- `Exec.bounded` needs `1 ≤ lim.word`;
- 38 lines of `Logic`, `Rules` and `Assigns` (28, 8 and 2, read line by line in the stage-2
  statement pack; the drafts estimated about 32) build or take apart `Ends` witnesses, so "the
  routines are untouched" holds for `Meets` and the library, not for those files.

The nondeterministic form's fill also needs one lemma not present today: a nondeterministic run
agrees with the deterministic one on states whose two transitions coincide. This is the
nondeterministic contract variant that §16 lists as later.

**Estimate** (not measured): about 9,500–15,000 lines beyond MIG-0a, made up of PROG-2
1.4k–2.3k, PROG-3 0.75k–1.35k and stage 2 6.1k–10.5k.

**Open questions for the user**, each with the drafter's recommendation (`NOTES.md` §6):
1. extend the RAM by a wrapper (recommended) or in place, which breaks about 50 configuration
   literals;
2. add `Exec`'s indices in place (option A, recommended, as §15c decided) or as a new relation
   (B);
3. `WordSizeComputable` with its two bridges (recommended), or `SpaceConstructible` directly;
4. `emit` appends "nonzero", and the footprint counts touched cells (both recommended as
   drafted).

**Answered (user, 2026-10-12): all four as recommended.** The RAM is extended by a wrapper, the
`Exec` indices are added in place (option A), the word size is `WordSizeComputable` with its two
bridges, `emit` appends "nonzero", and the footprint counts touched cells.

**Statement gate (2026-10-13):** `campaign/gates/10-stage2-statements/pack.md`. The maintainer re-elaborated
the landing form (0 errors; the only warnings are `sorry`s). It differs from the drafts in:
- **homes:** the wrapper in a new `Programs/WordRAM/Extended.lean`, below the compiler, because
  after PROG-2 the compiler emits `XInstr`; PROG-3's compiler-level statements as local
  modifications of the vendored `Simulation.lean` and `WholeProgram.lean`, because their proofs
  need private lemmas; stage 2 and its corollaries in a new topic `Complexity/RAMSimulation/`;
- **`startMem` is renamed `initMem`**, because the vendored compiler declares
  `Light.Compiler.startMem` and opens `WordRAM`;
- **footprints of at most `3n` cells**, so that `mem_P_of_decides` drops its cell bound;
- **the slice lemma and its space companion are stated** (`NDSlice`). The slice lemma is
  already proved, with a pointwise form of the same hypothesis, in C1's host draft
  (`campaign/items/c1/C1HostsDraft.lean.txt`, `Turing.NDTM.runWith_eq_fixChoice_runFrom`); the
  stage-2 pack does not say so. One copy lands, in `Nondeterministic.lean`, with C1's proof under
  the gated statement (maintainer note, 2026-10-13). **Both are proved** since C1's landing
  (PR #87, 2026-10-14);
- **PROG-2's edit list is longer:** under the wrapper, the compiler's code type becomes
  `List XInstr` at the sites the pack lists.

**Gate CLOSED** (round 1, 2026-10-14: 0 blockers / 0 majors / 4 minors;
`campaign/gates/10-stage2-statements/findings.md`, resolutions `campaign/gates/10-stage2-statements/resolutions.md`).
The homes, the namespace `WordRAM` and `initMem` are approved. PROG-3's compiler-level statements
(B1, B2) may land now, with their extended forms re-gated at PROG-2, or with PROG-2. The
auditor prefers `acceptProb` in a Complexity-side module. Next: the landing PR.

## 16. The foundation migration (user decisions, 2026-10-12)

**Why.** The user: "I really think we should invest effort into building code in the right way,
especially in this foundational stage." Seven read-only reviews of the tip `9827cc99` costed a
retroactive migration onto the §14/§15 style:
- the Build foundation and the machine core;
- the machine-level files that stay on Turing machines;
- the algorithm files that could become programs.

Their per-file figures are the restyling backlog (`backlog.md` §2, MIG/RS).

**Decisions (user, 2026-10-12).**
1. **The no-retroactive-migration rules are lifted for this migration**: §8's byte-identity
   bullet and decision 12.2's byte-identical `Primitives.lean`.
2. **Scenario B.** Proof bodies are swapped onto contracts, and in addition the duplicate
   statement families are retired: the R3 canonical `_run` rows, `counterLoopTM` next to
   `counterLoopTMVia`, `EmitIterEmbed`'s embedding, and `Codes2Tape`'s mirror. Their consumers are
   edited. Proof-body swaps under unchanged statements are gated by a freeze check, a replay and
   a fidelity gate. Each retired or changed statement needs a full statement gate.
3. **Savitch and `NSPACE ⊆ DTIME(2^O(S))` are algorithms at heart.** They are written as programs
   of the §15 language and converted by the RAM-to-`FinTM` compiler (stage 2). TM-intrinsic
   results are *not* recast as programs: Cook–Levin, TMSAT, NP ⊆ PSPACE's machine,
   Nondeterminism, the oblivious and hierarchy constructions, and the universal machine.
   **S1b**, in flight at machine level and proving `NSPACE ⊆ DTIME(2^O(S))`, `NL ⊆ P` and Ex 4.3,
   **finishes as briefed** (user, 2026-10-12: "Let it finish"). Once stage 2 and the
   configuration routines exist, it is re-derived as a program and its private host retired,
   with its public statements unchanged (MIG-19).
   *Outcome (fills-6, user: "Stop at this partial"):* S1b landed `NL ⊆ P` and Ex 4.3 proved
   modulo `NSPACE ⊆ DTIME(2^O(S))`, without a search host. MIG-19 is now the route for the
   simulation itself.
4. **Restyling is opportunistic, with a clear backlog** to chip away at: the RS items. Each
   row has its estimate, prerequisites and gate.

**The estimate** (ranges are the reviewers'; ESTIMATED unless marked):

| Bucket | Today | Net change |
|---|---|---|
| Foundation: Build (43,143) and the core (3,887), MEASURED | 47,030 | about −12.5k (−8k to −17.5k). That includes the `f2_` deletion, −7.6k to −8.3k at high confidence, and about 3.6k of new infrastructure |
| Machine-level files staying on TMs: universal, robustness, Nondeterminism, diagonalization and time hierarchy, oracle model, Mathlib bridge | 26.3k | about −4k to −5k: −3.7k from restyling, −1.7k to −2.1k from duplicates found, and +0.5k to 1.5k of extra infrastructure |
| Scenario B's statement retirements | | about −1k more |
| **Total** | **73k** | **about −17k (−12k to −23k)**. About 30k lines of proofs are touched and 4–5k are written new |

**What the contract structure must support** (§14 item 0). The survey revises the "time within
`T`" default taken from [AFM26]'s program logic:
- **exact time, with a no-earlier-exit cut, as first-class fields**, and "within `T`" derived
  from them. About 34 public Build statements carry cuts and about 33 state exact times. Seams,
  counter loops and the zone layer's `2p + 2` compose exact times;
- a **positive-duration field**, for the universal machine's block converse;
- an **endpoint function and a frame predicate**, with tape-indexed `SameOn`-style frames and
  `.keep` lemmas;
- **head envelopes**, both radius and interval forms, with space derived from them;
- the **input tape** (clamped moves, virtual input) and **output appends**;
- **transports**: state renaming (`Sum`/`Sigma`), R1 embedding, symbol lift, alphabet reduction,
  and the lockstep combinators of the robustness layer (decoration, parallel coding, folding);
- **later**, nondeterministic (`runWith`) and oracle-step variants.

From [AFM26] the design takes framing, spec-only calls and default-argument tactics; it does not
take the treatment of time.

**Programs for Savitch and `NSPACE ⊆ DTIME`** (decision 3) need one more planned component:
**machine-configuration routines in the language**. A configuration of a given (nondeterministic)
machine is encoded in memory, and routines enumerate its successors, or test the step relation,
from the machine's finite table. This is narrower than a general machine interpreter, since the
programs are built per machine.

Savitch's `O(S²)` space is **decided (user, 2026-10-12; §16b item 1)**: configurations are held
as single words, with word size `Θ(S)`, so that `O(S)` frames times `O(S)`-bit words fits the
planned bound of cells times word size. Stage 2 therefore takes a computed word size. A
bit-accounted space bound in the compile theorem was declined.

`NSPACE ⊆ DTIME(2^O(S))` is unaffected, since polynomial overhead on `2^O(S)` stays `2^O(S)`.

**Order of work:**
1. Item 0's statement phase and gate, with the requirements above.
2. The certain savings, which need no new infrastructure: named witnesses and the `f2_` deletion
   (MIG-1), then the known duplicates (MIG-2 to MIG-10).
3. Contract instances and tactics, grown against the first migrated file; then rebasing the
   composition-heavy files (MIG-11 to MIG-17).
4. The asymptotics port (MIG-18).
5. The RS items, opportunistically.

**12.2c** (plan §4e) is folded into this migration. Its items are subsumed, moved, kept as MIG-20
and MIG-21, or lapsed, as recorded at the head of the 12.2c tasklist. **MIG-0 and MIG-1 now
precede §13d G2** (user, 2026-10-12), reversing "G2 comes before the Catalog split".

New and unfinished work is written in the new style from the start. Deliveries now in flight
in the old style (record tables, W2-S, B5a canonizer and H1, B4, S1b) join step 3.

### 16a. MIG-0, the contract structure: statement draft and decisions (2026-10-12)

**A sorried statement draft of `Build/Contract.lean` was written and fit-tested** (maintainer,
2026-10-12). It was informed by a read-only inventory of every public contract in `Build/`
(about 150 run statements: 24 exact closed-form times; about 45 cuts that include time `0` and
4 that do not; 25 interval and 12 radius envelopes; no frame predicate anywhere, and frames
written in four idioms).

**The structure** `Turing.Contract M entry exits ι x`:
- a precondition, an **exact time**, an **endpoint function** and per-tape head intervals
  `[lo, hi]`, all functions of a data index `i : ι` (the word or fields the module reads) and the
  start configuration;
- proofs: the run reaches the endpoint at that time; the endpoint is at an exit; **no exit is
  reached earlier, with the cut including time `0`**; and the heads stay in their intervals.
  Exits form a set, so single anchors, verdict pairs, loop exits and halting are one structure;
- derived: "within `B`" (`within`) and the per-tape space bound (`spaceUsedByTape_le`, through
  `spaceUsedByTape_le_card_Icc`); positivity is a predicate.

**Decisions (user, 2026-10-12):**
1. **Universe `Type`** for the alphabet, the states and the data index: the universe of
   `FinTM`, `phaseHostTM` and `counterLoopTMVia`. UNIV-1(a) stays an optional generalization.
   Raw-layer exports that move into `Build/Embed` and `Build/Seam` take their host modules'
   universes (`Type*`; MIG-0b round 1, finding 2); the contract structures keep `Type`.
2. **Frames are a derived layer**, not a field. The endpoint already states the frame as
   `{ d with … }`. The layer adds `Cfg.SameOutside` (a per-tape footprint), its composition,
   `.keep` lemmas for stored words and blank tapes, and `Contract.Frames`.

**Compositions, as thin wrappers over the existing rows:**
- `trans`: first-exit sequencing on one machine. It is not a general `RecordRun` concatenation
  (MIG-0a gate, round 1, major; see below);
- `seq`: the R2 seam, time `t₁ + 1 + t₂`;
- `inPhase`: one phase inside the phase host, whose redirect targets lie in other phases (a
  sufficient condition: the run must avoid every redirect target up to its endpoint);
- `embed`: the R1 embedding, with unselected tapes framed and output appended;
- `branch`: the two-way seam;
- `ReturnContract` with `release`: for rows that return to their anchor, whose cut starts at
  time `1`, such as the advancing writer. The install and emit calls quantify separate entry and
  exit states that may coincide, so with arbitrary witnesses they split on `entry = exit`
  (corrected at the gate, round 1, minor 5).

**Fit test.** `trans`, `seq`, `inPhase`, `embed` and `embedEmitCfg_select` are proved with no
statement change and no extra hypothesis, on the standard three axioms. So is the instance
`clearTM_contract`, R3 clear repackaged from `clearTM_run_ofCfg`. A second fit test then
proved the rest: the frames layer (the `SameOutside` lemmas are nearly definitional),
`clearTM_contract_frames` (the footprint is exactly where the endpoint writes blanks), `release`
and `branch`. **The whole MIG-0a draft is proved: 843 lines, 0 errors, 0 warnings**
(`campaign/items/mig0/Contract-draft.lean.txt`).

Further observations from the fit tests:
- **Liveness is a lemma.** A contract's run is live strictly before its time, from the cut and
  `exit_mem`, since a halt would persist to the endpoint. `branch` needs it; promote it as
  `Contract.live`.
- **`branch`'s halting exit is untagged.** If both continuations may halt, a halted endpoint
  does not say which ran. The statement is still correct.
- **A third export:** a pointwise `seamReleaseTM_runFrom_pos`. The release's envelope went
  through `seamReleaseTM_visitedByTapeHead`, because the pointwise lemma is private.
- **Ergonomics:** a `@[simp]` unfolding lemma for `Frames` and `SameOutside`, so that `rw` sees
  a footprint's `if` without a `show`.

The test found two missing public exports, both additive:
- `embedEmitCfg_unselected_tape` and `_pos` (`Build/Embed.lean`). The proof of
  `embedEmitCfg_select` worked around their absence through `embedEmitTM_frame` and a trivial
  machine;
- a right-segment seam lemma (`Build/Seam.lean`), to replace the private `seamComp_right`. It is
  needed for set-valued exits; `seamCompTM_firstReturn_ofCfg` excludes only one target.

**Scope, in two increments:**
- **MIG-0a:** the structure, the derived lemmas, the frames layer, `trans`, `seq`, `inPhase`,
  `embed`, `branch`, `ReturnContract` with `release`, `Contract.live`, and two exports
  (`embedEmitCfg_unselected`, `seamCompTM_runFrom_right`); the pointwise release export is
  deferred to MIG-0b;
- **MIG-0b:** revised after the gate's round 1, below.

**MIG-0a gate, round 1** (2026-10-12: 0 blockers, 1 major, 5 minors; `campaign/gates/04-mig0a/findings.md`,
resolutions `campaign/gates/04-mig0a/resolutions.md`). No proved statement was found false. The major is
about the migration interface: a first-exit `Contract` does not directly replace three kinds of
existing specification, so the direct-replacement claims of MIG-12 and MIG-15 were wrong.
- **Segments.** `CfgRecord`'s `RecordRun` is a fixed-length run that avoids a forbidden verdict
  set; its endpoint need not be a first visit, and `recordRun_trans` concatenates on one machine
  with no dispatch step. The auditor's example: a machine idling at `a` gives a length-2 segment
  from `a` to `a`, which neither a positive `Contract` nor a `ReturnContract` can package.
- **Return-or-escape rounds.** `RecordTable`'s `rt_find_round_entry` and the counter loop's rounds
  end either back at their anchor or at a distinct escape, with positive cuts against both. A
  `Contract` fails its time-zero cut there, and a `ReturnContract` excludes the escape.
- **Joint trajectories.** `CounterLoop`'s `counterSpan` constrains the whole head vector along a
  run. Per-tape intervals cannot express a relation such as "the two heads are equal".

`Contract` stays the first-exit specialization. **MIG-0b** therefore covers, before any
dependent migration:
1. a **segment layer**: fixed-length segments avoiding a forbidden set, with same-machine
   concatenation (the `RecordRun` pattern), and a bridge to `Contract` when the endpoint is a
   first exit;
2. a **round layer**: return-or-escape rounds with positive cuts against the anchor and the
   escape, and the counter loop's composition over them;
3. a **joint-trajectory layer**: a relation on the head vector along the run, derived like
   `Frames` and preserved by the compositions;
4. the **layering split**: a core contract module that `Loop` and `CounterLoop` can import
   (round 1, minor 2), with the adapters and routine instances above it; the two exports move into
   `Build/Embed` and `Build/Seam` then. Round 2's import repair found that the file needs `Seam`,
   `Catalog` and `Mathlib.Tactic.Linarith` (which `CounterLoop` used to supply indirectly), so
   `CounterLoop` is no longer in its closure, but `Loop` still is, through `Catalog`. The core
   part needs only the machine core, apart from `MultiTapeTM.spaceUsedByTape_le_card_Icc`, which
   lives in `Catalog` and moves down first. **Revised by MIG-0b round 2** (2026-10-13;
   `campaign/gates/15-mig0b/pack-r2.md`, NOTES-r2 §3):
   - `spaceUsedByTape_le_card_Icc` and `workTapePos_runFrom_mem_Icc` move to `Finite` (not
     `Deterministic`);
   - `runFrom_mapState_of_agreeOn` moves to `StateRenaming`, which then imports `Simulation`;
   - MIG-0a's private helpers are deleted;
   - `Build/Seam` promotes its polymorphic release and composition lemmas;
   - `AlphabetReduction` imports the core;
   - the Embed exports are stated over `Type*`.

   The core's closure is `Configuration`, `Deterministic`, `Finite`, `Simulation` and
   `StateRenaming`;
5. the pointwise release export `seamReleaseTM_runFrom_pos`;
6. the symbol lift (through `Cfg.decodeSymbols`), state renaming along an embedding
   (`runFrom_mapState_of_agreeOn`), and the alphabet-reduction and robustness-lockstep adapters
   (round 1, note 20);
7. the tactics, and the auditor's suggested sanity lemmas: the zero-time characterization
   (`time = 0 ↔ some entry ∈ exits` on admissible starts) and positivity of the compositions;
8. **the R1 reconstruction lemma** in `Build/Embed`, at the layering split (the wave-1 fill gate's
   major F1, acknowledged by the user): from the selected-bank projections and the unchanged
   ambient frame, equality of an embedded configuration, cited by `OracleSim.oracleBankCfg_eq`,
   `Loop.emCall_exit_fixed`'s local frame and `CodeSimulator.canonEmbedEq`.

MIG-0a's round 2 audits the corrected records and the documentation repairs; no statement or proof
of the file changes. **Round 2 closed the gate** (2026-10-13, 0 blockers / 0 majors / 1 minor;
`campaign/gates/04-mig0a/findings-r2.md`). Its acceptance obligations for MIG-0b's statement gate:
- the segment layer keeps zero-length segments, the inclusive envelope and the actual
  configuration seam (`RecordRun`'s shape);
- `counterSpan` is a segment property (no entry or endpoint constraint; it admits time zero, which
  `counter_rounds` uses), so it migrates to the segment and joint-trajectory layers; positive
  return-or-escape rounds describe the loop body's interface;
- `splitSafe`'s avoidance holds at every time through the endpoint, so it uses the segment layer
  with endpoint-inclusive avoidance, and first-exit `Contract`s apply only where a first exit is
  proved (`SafeRun`, in `Build/EmitIterEmbed.lean`, avoids only strictly before the endpoint: a
  plain segment);
- both round rows also require the round's interior to be live;
- the joint-trajectory property holds for general segments, and keeps the counter loop's single
  shared round and time witness for all body heads, its exact endpoints, bounds and liveness.

**MIG-0b gate, round 1** (2026-10-13; `campaign/gates/15-mig0b/findings.md`): **0 blockers / 2 majors /
4 minors, gate open.** The segment, round and trajectory layers meet round 2's acceptance
obligations above, and no proved statement is false. Both majors concern the landing plan:
- the planned split strands private helpers (`mem_hull_left`, `mem_hull_right`,
  `runFrom_state_none_mono`) and a fit-namespace bridge that kept modules use;
- the release export `seamReleaseTM_runFrom_pos` fixes universes to `Type`, narrower than the
  polymorphic `seamRelease_run_pos` it replaces.

**Round 2 CLOSED the gate** (2026-10-14: 0 blockers / 0 majors / 3 minors;
`campaign/gates/15-mig0b/findings-r2.md`). Round 2 (`campaign/gates/15-mig0b/pack-r2.md`, re-run at `1781a230`): a real
split, cut-checked without the fit namespace; the polymorphic release; and the minors (an
entry-compatibility lemma for `Contract.lockstep`, the release's wording, the alphabet admission's
sketch and reference, and records).

### 16b. Five route decisions (user, 2026-10-12)

The user took the five open route questions together, each as the maintainer recommended (plan
§4e, decision log, 2026-10-12).

**Update (2026-10-14).** Hydroxyi's ARM merge (`8c23f3bc`) proves the customers of items 1
(Savitch at polynomial space), 2 (`TQBF_PSPACEHard`, without RD-2's codec) and 4 (`PATH ∈ NL`,
NL = coNL). The user held RD-2's fills and paused stage 2 (backlog RD-2, PROG-4); general
`savitch` stays open. Item 3's "S1b's private copies re-pointed in the same PR" was carried
out by the B6 hosts' landing (PR #92, merged 2026-10-14): seven private copies removed, five
re-pointed. ConfigGraph's remaining 11 private `s1b_*` declarations have no consumer, and the
payback PR deletes them (backlog §1 ARM-1).

1. **Savitch's space: words of `Θ(S)` bits.** A configuration of the simulated machine is one
   word, so a recursion level holds `O(1)` cells, and depth `O(S)` gives `f = O(S)` cells. Stage
   2's space bound stays cells times word width (§15a), which gives `O(S·(S + log S)) = O(S²)`.
   The alternative, charging each cell for the bits it holds, was declined: every cell still pays
   an `O(log S)`-bit address, so it reaches `O(S²)` only with packing as well. Consequences:
   - **Stage 2 takes a computed word size.** `W` is a function of the input length that the
     compiled machine computes within its space bound: `c·log n` for P and L (from the
     input-length counter, R8.5c) and `c·S(n)` for Savitch (from `S`'s constructibility
     witness).
   - The machine-configuration routines work on packed words, using `half` (PROG-2).
   - With `W = Θ(log n)` and packed configurations, the drafted bound already gives `O(S²)` for
     polynomial `S`. That suffices for `PSPACE = NPSPACE`, but not for `savitch`, which is stated
     for every space-constructible `S`.
2. **B4a is restated in place, over H6.** `exists_adjacency_codec_cnf` becomes public
   definitions of the codec and its three CNFs with closed-form variable indexing, and theorems
   about them in place of the `∃`. Its present formulas index variables through
   `Fintype.equivFin` over types that depend on `n` and `s`, so no machine or program can be
   proved to emit them (Finding A; the `TQBF_PSPACEHard` docstring: "The packaged existential
   supplies no algorithm"). The indexing is designed with H6 (§14), so that Cook–Levin and TQBF
   share one scheme.
   - It changes an audited public statement: a statement gate, then a re-fill. Its only consumer
     is the open `TQBF_PSPACEHard`.
   - Hardness also needs Tseitin on `Std.Sat.CNF ℕ`, correct for every prefix assignment.
   - Whether the `ψᵢ` emitter is a machine (H6) or a program with `emit` is decided with B4
     hardness's design.
   - **Designed (2026-10-12):** `campaign/items/rd2/RD2-design.md`, with a sorried statement draft,
     `campaign/items/rd2/RD2Draft.lean.txt`. The draft elaborates with 0 errors and 36 sorries;
     11 of its theorems are proved. It proposes:
     - the H6 kit as `Complexity.FormulaKit`: block variables, a truth-table gate template with
       closed-form wires, ledgers, and emission over `polyTimeComputable_emitIter`;
     - a generic Tseitin-after-prefix lemma, with its instance for `DAGCircuit.toCNF`;
     - `Complexity.ConfigCodec`: a closed-form layout of width `2n + 4 + Q + 3k(2s + 1)`,
       clause lists ordered by `List.range`, the old statement's clauses as 11 theorems, and new
       uniformity theorems.

     About 820 of the old proof's roughly 1,700 lines survive verbatim (measured at 703 by the
     statement pack's migration list). Estimate: 2.5k–3.6k lines landed; a statement gate, then
     two fills.
   - **Answered (user, 2026-10-12): all five of the note's recommendations.**
     - `exists_adjacency_codec_cnf` is retired; no proof uses it.
     - The uniformity theorems are part of RD-2, as the fill RD-2b.
     - The ψ matrix is a guarded CNF, so the private Tseitin lemmas of the colleague-owned
       `DAGCircuitSat.lean` are not needed.
     - **The ψ emitter is a machine,** on H6 and the polynomial-time closure algebra.
     - The transition gates are truth-table templates, as in Cook–Levin.

     **Statement gate (2026-10-13):** `campaign/gates/11-rd2-statements/pack.md`. The landing form drops the
     Tseitin instance (decision 4), and adds 17 theorems: the kit's cost ledger, so that the
     private twins merge; the fragment and gate emission forms; unary index arithmetic, because
     the codec divides by `2s + 1`; and the port contract. The prefix-truth lemmas are proved.
     **CLOSED** (round 1, 2026-10-14: PASS, 0 blockers / 0 majors / 2 minors;
     `campaign/gates/11-rd2-statements/findings.md`). Next: the landing PR, then RD-2a and RD-2b.
3. **B6 takes the window route, and `space_universal` is restated forward-only.**
   - **The window route.** `space_hierarchy`'s diagonalizer runs one fixed self-simulating
     universal machine `U₀` inside a window of radius `a·g(n)`, on the configuration-record rows,
     stopped by a configuration-count clock, and flips `U₀`'s verdict. It needs `U₀`'s forward
     direction with a space ledger, the windowed runner H3 (record-table rows 17–18, in flight),
     the step block H2 and the native input device of H5. The sketch's budget loop, head caps,
     interval counters and probe/replay go.
   - **Why:** the chapter-1 interpreter cannot serve (Finding B). It tracks the input head in
     unary on its fourth tape, so that tape uses one plus the largest simulated input position
     reached: `Θ(n + 1)` cells on a full scan. So it cannot guarantee `O(S(n))` space uniformly
     for sublinear `S`, which the present sketch's premise needed (wording corrected at the RD-3
     gate, minor 4).
   - **`space_universal` keeps only its forward clause,** as [AB09, Exercise 4.1] states it (p. 93,
     checked 2026-10-12): if `M_α` halts on `x` before using `t` cells of its work tapes, then
     `SU(α, t, x) = M_α(x)`, and `SU` uses at most `C·t` cells. The `[false]` clause goes, and
     with it the interval counters, the core-count clock and the probe/replay. It still needs a
     code-first universal that reads its input through a binary-position device (H5). (Superseded
     2026-10-13: the bounded-prefix ruler device, with `space_universal` at `C·s`; decisions
     B1–B2.)
   - The sketch drops its stale "space-preserving normal form" obligation: the normal form is
     proved (`Turing.FinTM.one_work_tape_binary_spaceUsed`, `Robustness/SingleTape.lean`), but
     two small steps around it were not, and they were fill obligations: the space clause of
     the coding step `exists_codeTM`, which is time-only, and a decider's space bound at every
     time (the normal form needs it at every time; `DecidesInSpace` bounds it at the halt).
     Both are proved in the host draft below.
   - `U₀` and the windowed runner had no statements before the host draft below. `U₀` is a
     public row built from H2 and H5, not a private host of this proof. The runner's contract
     exposes three outcomes (halt, window exit, clock exhaustion). `counterLoopTMVia` has one
     optional early body exit plus clock exhaustion, so H3 can merge halt and window exit into the
     early escape and tell them apart afterwards from the retained record (the RD-3 gate, minor 3).
   - **RD-3's statement gate passed** (2026-10-13, 0 blockers / 0 majors / 4 minors;
     `campaign/gates/05-b6-restatement/findings.md`). `space_universal` keeps its `+ logSpace |x|` addend for
     now; the auditor's addend-free `C·s` route (a bounded-prefix input device, a unary ruler of
     the header's length) is to be decided when H5 is gated.
   - **Host statements drafted (2026-10-13):** `campaign/items/b6hosts/` (design note, and the
     draft `B6HostsDraft.lean.txt`: 0 errors, 10 sorried machine contracts, 43 declarations
     proved). It contains:
     - **H3:** a pure specification `windowRun` with three exits; a step clock shared with C1,
       `exists_stepClockTMVia`; and a clock-agnostic runner for `space_hierarchy`,
       `exists_configWindowRunnerTM`;
     - **H5:** a native device, and a bounded-prefix ruler device with a host transformer;
     - **`U₀`:** a startup, and a forward ledger `C_α·(s + 1)`;
     - **the two fill obligations above, both proved:** `exists_codeTM_spaceUsed` and
       `ComputesInTime.spaceUsed_le_of_halt`.

     Open questions for the user: the note's §10.
   - **Answered (user, 2026-10-13), all as recommended:** `space_universal` is strengthened to the
     book's `C·s` in the B6 hosts' statement-gate pack, through H5's ruler device; no
     binary-position device (its registry row stays); the public `outSummaryCode`/`summaryTag`
     land in `ConfigGraph.lean`, with S1b's private copies re-pointed in the same PR; the
     configuration-count runner and its bound go to a new `SpaceComplexity/WindowClock.lean`, so
     that `Build/WindowRun.lean` imports nothing from `SpaceComplexity`; the contracts are gated
     as `∃` statements, with named machines at fill time.
   - **Statement gate (2026-10-13):** `campaign/gates/13-b6-hosts-statements/pack.md`. Changes from the
     draft:
     - the ruler host is a block simulation (H2-S round 1, finding 2);
     - `U₀`'s sketch uses the reset-output invariant (finding 4);
     - `exists_stepClockTMVia`'s trajectory clause also carries the body tapes, input position and
       output, which the runner's silence and restoration need; C1's form `exists_stepClockTM` is
       unchanged, so C1's pack only re-points its citation at landing;
     - window containment and the B6 summary instance move to `WindowClock`.
   - **CLOSED** (2026-10-14: PASS, 0 blockers / 0 majors / 5 minors;
     `campaign/gates/13-b6-hosts-statements/findings.md`). The step clock keeps `+2`; the runner stays
     clock-agnostic. Next: the landing PR.
   - The shortcut through a space ledger for the time hierarchy's `diagSim` is not taken.
   - The restatement and the re-routed sketches go through a statement gate.
4. **C2 is written as programs with coins.** `PATH ∈ NL`, Immerman–Szelepcsényi and their
   corollaries are programs of the language using read-once `coin` (PROG-2), compiled by stage 2.
   This removes C2's dependency on the nondeterministic `LogProg` extension asked of Hydroxyi
   (plan §2.5; `backlog.md` §2, *ARM extensions*). Stage 2 therefore needs, besides item 1's word
   size:
   - **a nondeterministic form:** each `coin` is one choice step of a `FinNDTM`, with time and
     space bounds uniform over the coin streams (§15c);
   - **a logspace grade:** `O(1)` cells and `W = O(log n)` give space `O(log n)`. This needs the
     input read in place (PROG-2) and the footprint along runs (PROG-3).

   `PATH_NLComplete`'s hardness half needs only the deterministic layer.
5. **§13d G2–G4 stay in the campaign**, after MIG-0b, so that the mapped sweeps, the carrier's
   rows and the rebalance rows are stated as `Contract`s from the start. They share no file with
   stage 2 and can run alongside it. The two open zone rows (`exists_zoneShiftInTM`,
   `exists_zoneShiftOutTM`) retire through the G3/G4 gate, as §13d planned.

**Stage 2's statement** (`backlog.md` PROG-4), drafted together with PROG-2 and PROG-3, therefore
carries a computed word size, deterministic and nondeterministic forms, and a space bound good
enough for L.

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | The `j`-th block of `c` bits of a coin string, `(r.drop (j * c)).take c`, stated three times: `coinSlice` (`ZeroKnowledge/GraphIsomorphism.lean`, ch. 2–4), `Authentication.coinBlock` (`Authentication/Lamport.lean`, prong A), `Protocol.phaseSlice` (`Composability/SequentialZK.lean`, prong C) | found by the Lamport worker and the maintainer | Before the ch. 5–8 statement gate: one copy in a shared upstream module, with its length lemma, used by all three. |
| DL-7 | `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`: `Authentication.ofFn_padFin_of_length` (`Lamport.lean`) is the equal-length case of ch. 2–4's `ofFn_padFin_of_le` (`Asymptotic/Collections.lean`); `Composability.length_eval_of_length` (`CCA2Scheme.lean`) repeats the step inline | found by the Lamport worker | Before the ch. 5–8 statement gate: use `ofFn_padFin_of_le (le_of_eq h)`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03l-r1.md =====

# Gate 03l (the `Randomized/Build/` machine layer): round 1 resolutions

- **Round 1:** findings `findings/gate03l-findings.md`, verbatim, SHA-256
  `093149a928c07d238af402b5b25c56274bc2853858cd716574c699ef8c6c234b`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 1 major (#1), 3 minors
  (#2–#4), 210 notes (#5–#214).**
- **Review:** `review/gate03l-review.md`: all four findings true, severities kept. Minor 3 was
  understated: consumers already unfolded the definitions. Its §5 classifies the 210 notes, and its
  §6 lists six items the auditor missed (M1–M6 below; §6.1 would have been a major).
- **Rulings (user, 2026-11-05):**
  - **R-03l-1, option (B):** clean up the copies of `main`'s code in gate 03's repair PR, editing
    main-owned files on this branch.
  - **R-03l-2, option (A):** `StateLoop.orbit_zero` and `orbit_succ` keep `@[simp]`, on G3-6's
    terms.
  - **G3-5 (A)** for the duplicates.
- **Repair:**
  - **Major 1:** evidence only. `evidence-repairs/03l/axioms.log`, at
    `af91d53a414cdad6bbb61cecdc13f5e0e956d0b1`; the six files were unchanged since the audited
    head.
  - **Everything else:** PR [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203), gate 03
    clean-up part 1 (head `f29be161cd86cfc3a9c38bd203bfa095b4974086`, merged by
    `8ec28f130eaca5f7d7dc756953bde0807d41b7df`). Its evidence is
    `evidence-repairs/03l-cleanup1/`: the worker's report, the replay (134 modules), axioms (268),
    the seal with controls, lint before and after, and the statement diff, plus the maintainer's
    re-check of 11 key modules.
- Line numbers below are at the pin of round 2; Lean paths are under `TCSlib/Complexity/`.

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major | **Fixed (evidence).** The full `#print axioms` of the six files' 90 public theorems and lemmas and of 16 consumers in `Randomized/Repetition.lean` and `Randomized/Primitives.lean` (106 distinct declarations): none depends on `sorryAx`, so none uses `main`'s five `Loop.lean` admissions. The staging tool now prints every public theorem of a pack's files (`--full`), and words an empty selection "not applicable", never "0 of 0" (`evidence-repairs/03l/gate03_stage.py.txt`). Round 2's attestation is generated that way. |
| 2 | minor | **Fixed** (#203, item G). A dated as-built erratum is appended to DESIGN §2.6 (`briefs/pass-shelat/DESIGN.md`, "As-built erratum (2026-11-05, gate 03l, minor 2…)"); the frozen text is unchanged. It records the new-output guard with the counterexample to the old one, the actual-pair invariant, the release-flag stop, the padding, the multi-module host (now H14), the two-state copier, the budget `A·(2n + 7 + P n)^D` and the `≤` counter test. §2.4 notes that `PairSplit` uses one work tape. `Repetition.lean`'s construction plan and the sketch of `polyTimeComputable_iterateFind` describe the built route (missed item M2). |
| 3 | minor | **Fixed** (#203, item E). 38 reading lemmas, none `@[simp]`, all `rfl` or `Iff.rfl` except `gstepBound_eval`. The review's 39th, `blk_eq`, is unnecessary because `BlockMapLoop.blk` is private, as recommended. The host's lemmas now sit in `TuringMachine/Build/ModuleHost.lean` (`clean_iff`, `state_eq`, `entry_eq`, `hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`); `copyTM_k`, `hostRet_*`, `hostCtrl_eq` and `hostTM_eq` are in `IterateFindHost.lean`. 18 unfolding sites are re-pointed: the review's 16, plus two in `polyTimeComputable_blockMap` that the seal found. The seal of 8 consumer files passes with controls (`evidence-repairs/03l-cleanup1/seal.log`). Check 8/8b is clean on the six files and the new host file (`lint-after.log`). |
| 4 | minor | **Fixed** (#203, item F). The 13 label docstrings now state their results ("The map `v ↦ …` (…) is polynomial-time computable"; `param_poly` adds that any first component works). `host_clean` (now `Turing.ModuleHost.host_clean`) states the bounded-call contract, and `Clean`'s docstring adds `0 < M.k` and the positive first halt (note 81). The optional `orbit_eq` wording is done. |
| 5–20, 22 | note | **No change** (general: source comparison, budget arithmetic, fresh coins, the `Loop.lean` dependency, inventory, the run-3 record, the adversarial instantiations, finite checks). Note 6's optional item, that `PairSplit` uses one work tape, is in DESIGN §2.4 (#203). |
| 21 | note | **Fixed** with #2. |
| 23–37, 39–53, 56–71, 73, 75–80, 82–83, 86–91, 93–97, 103 | note | **No change** to statements (private declarations that agree with their docstrings). Note 65 is fixed: `stepWord_verdictWord` no longer says "admissible". The copy rows (75–91, 103, 41–46) are resolved by M1. |
| 38, 54, 72, 74, 84, 85, 98, 104, 105, 107–111, 114, 120–122, 127–130, 135–139, 145–148, 156–164, 174–182, 186–196, 206–214 | note | **No change** (public declarations that agree with their docstrings). For 84, 85 and 104 the copies are resolved by M1. |
| 55, 81, 99–101, 125, 126, 131–134, 140–142, 149–152, 165–169, 183–185, 197–202 | note | **Fixed** with #3. Note 55 is `IterateFind.step_eq`, which bridges `IterateFind.step` to `guardedStep` (M4). Note 81 is `clean_iff` plus the docstring (#4). Notes 197–202 are `BlockMapLoop`'s lemmas, under the namespace renamed per M3. |
| 106, 143, 144, 153–155, 170–173, 203–205 | note | **Fixed** with #4. |
| 92, 102 | note | **Fixed** (#203). `copyTM` has `@[simps (config := { isSimp := false }) k]` (`copyTM_k`); the host machine has `simps k tm_q₀` (`ModuleHost.hostTM_k`, `hostTM_tm_q₀`). |
| 112, 113, 115–119 | note | **Scheduled:** clean-up part 2, DL-17. `StateLoop`'s `headBit_poly`, `tail_poly`, `isNil_poly`, `not_poly`, `or_poly`, `xor_poly` and `length_pairFstD_add_pairSndD_le` restate `main`'s lemmas, and about 23 files use them, some of which #195 changes. |
| 123, 124 | note | **Recorded** (R-03l-2): `orbit_zero` and `orbit_succ` keep `@[simp]` (`Randomized/Build/StateLoop.lean:186, 190`). |
| M1 | (review §6.1) unledgered duplication, a major until ruled | **(a) Fixed** (#203, DL-16): one public host `Turing.ModuleHost` (registry row H14, `machine-library-design.md` §14), consumed by `ClassNP/SAT.lean` and `IterateFindHost.lean`. Both copies are deleted, and SAT's public statements are unchanged. **(b) Fixed** (#203, DL-18): `UnaryMul` uses `PairSplit`'s parser (`Turing.PairParse`). **(c) Scheduled:** part 2 (DL-17). **(d) Recorded:** in row H14, `copyTM` is recorded as a parallel routine to `EmitIterBody`'s private copier, not a copy. |
| M2 | (review §6.2) `Repetition.lean`'s stale construction text (pack 03a's file) | **Fixed** with #2 (#203, item G). |
| M3 | (review §6.3) a latent clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` | **Fixed** (#203, DL-19): renamed `StateLoop.BlockMapLoop`, with 17 declarations' statements kept. |
| M4 | (review §6.4) `IterateFind.step` restates `guardedStep` | **Fixed:** both definitions are kept, and `Repetition.lean`'s bridge goes through `IterateFind.step_eq` instead of `rfl`. |
| M5 | (review §6.5) the lint attestation used the presence-only lint | **Fixed:** #203's evidence runs `campaign_style_lint.py --check8b` before (5 WARN) and after (none on these files). Round 2's attestation records the same. |
| M6 | (review §6.6) two `@[simp]` attributes outside G3-6's list | **Recorded** (R-03l-2); see 123, 124. |

**Statement changes in the repair** (#203's `statements.md`):
- The host declarations moved to `Turing.ModuleHost` and were generalized: `Clean`, `clean_install`, `clean_emit`, `HostState` → `State`, `hostEntry` → `entry`, `host_call`, `guard_add`, `host_clean`. `host_call` and `host_clean` now exclude every control state, not only the anchor.
- `IterateFind.hostRet`'s type and `IterateFind.hostTM` (now an abbreviation) follow from the move.
- 17 declarations are renamed by M3.

No statement of `exists_pairSplitTM`, `exists_unaryMulTM`, `IterateFind.polyTimeComputable_find` or the `Repetition.lean` headlines changes.

**Found by the repair:** for clean-up part 2, five old `| zero => rfl` reads of `StateLoop.orbit` in files that part 2 edits (`QUEUE.md`). Separately, ledger row DL-20, `Loop.lean`'s private `loop_first_halt`, is the same lemma as `ModuleHost.first_halt`. It is **noted, and paid back at the `main` landing**, not in part 2: `Loop.lean` is `main`'s file, upstream of the host, and the payback moves `first_halt` and `live_prefix` into it (corrected on gate 03l round 2, finding 4, so that this file and the ledger agree).

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03l-pack-r2.md =====

# Gate 03l ([PS10] ch. 2–4, the `Randomized/Build/` machine layer, and the clean-module host), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e28773ef3bda6f7b4b112ec1657427bfef01e374` (the branch after #201 and #203 merged; its Lean files are #203's head `f29be161`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 1 major (#1, the empty axiom attestation), 3 minors and 210 notes**; the review kept the severities and added six missed items (M1, unledgered duplication, would have been a major) (`gate03l-findings.md`, in the bundle,
  verbatim).
- **The repair:** major 1 by evidence (`evidence-repairs/03l/axioms.log`); everything else in gate 03 clean-up part 1, #203 (DL-16: the clean-module host harvested from `ClassNP/SAT.lean`'s private layer into public `Turing.ModuleHost`, registry row H14, consumed by `SAT.lean` and `IterateFindHost.lean`; DL-18: `UnaryMul` uses `PairSplit`'s parser; DL-19: `BlockLoop` renamed `BlockMapLoop`; minors 2–4), per ruling R-03l-1 (B). The full delta is `evidence-r2/03l/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03l-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03l-review.md` (in the bundle).
- **The deliverable:** **`gate03l-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03l-r1.md` (the
   findings, grouped as the review grouped them, and the review's missed items `M1`, …) say
   whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR (clean-up part 2,
     after #195), and the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03l/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement, rename and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.
3. **It gates the host's contract** (registry row H14, `machine-library-design.md` §14: "contract
   gated at gate 03l's delta round"). Restate `Clean`, `host_call` and `host_clean` in your own
   words; say whether the contract is generic in what its two consumers vary (the modules, the
   control states and their table, the return map, the start state), whether its time and
   no-anchor-visit clauses are what a third consumer would need, and whether `SAT.lean`'s
   instantiation (section B of the diff) preserves SAT's public statements.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** The host declarations moved to `Turing.ModuleHost` and were generalized (`Clean`, `clean_install`, `clean_emit`, `HostState` → `State`, `hostEntry` → `entry`, `host_call`, `guard_add`, `host_clean`; `host_call` and `host_clean` now exclude every control state, not only the anchor); `IterateFind.hostRet`'s type and `IterateFind.hostTM` (now an abbreviation) follow; `StateLoop.BlockLoop` → `StateLoop.BlockMapLoop` (17 declarations, statements kept); `BlockMapLoop.blk` is private. The old → new list is `evidence-repairs/03l-cleanup1/statements.md` (in the bundle). No statement of `exists_pairSplitTM`, `exists_unaryMulTM`, `IterateFind.polyTimeComputable_find` or `SAT.lean`'s public theorems changes.
- **New public declarations:**
- **the host** `Turing.ModuleHost` (new file): `Clean`, `clean_iff`, `State`, `state_eq`, `entry`,
  `entry_eq`, `hostTM` (with `simps k tm_q₀`), `hostTM_step_inl`, `clean_install`, `clean_emit`,
  `host_call`, `host_clean`, `guard_add`, `first_halt`, `live_prefix`, `request_budget`;
- `IterateFindHost.lean`: `hostCtrl`, `hostCtrl_eq`, `hostRet_zero` … `hostRet_four`, `hostTM_eq`,
  `copyTM_k`;
- the parser `Turing.PairParse` (`PairSplit.lean`): `cfg` (with `simps`), `cfg_inputSymbol`,
  `cfg_workTapeSymbols`, `cfg_congr`, `apply_cfg_stay`, `apply_cfg_advance`, `parse_first`,
  `parse_block`, `rewind_run`;
- the reading lemmas: `IterateFind.step_eq`; `StateLoop.gstep_eq`, `gstepBound_eval`,
  `IterLoop.{start,step,acc,out}_eq`, `EmitLoop.{start,step,out}_eq`;
  `MajLoop.{start,step,acc,out}_eq`, `XorLoop.{start,step,acc,out,rounds}_eq`,
  `EqLoop.{step,out,flag}_eq`, `BlockMapLoop.{start,step,acc,out,rounds}_eq`.

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03l-findings.md`, `review/gate03l-review.md`, `resolutions-03l-r1.md`, `evidence-r2/03l/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Complexity/Randomized/Build/{IterateFind, IterateFindHost, PairSplit, StateLoop, StringLoops, UnaryMul}.lean`, `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (new) |
| Context | `03l-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows), `machine-library-design.md` §14 (row H14), `evidence-repairs/03l-cleanup1/statements.md` and `seal.log` |
| Out of scope | tactic proofs; clean-up part 2 (after #195) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/l2/` in the bundle)

### Attestation results at `e28773ef3bda6f7b4b112ec1657427bfef01e374` (evidence under `evidence/l2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 27 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 139 prints of every public theorem and lemma in this pack's files:
   139 use only the standard axioms, and 0 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 7 files.

The replay is the 416-module replay at `af91d53a`, overlaid by the re-check at #201's head
(`evidence-repairs/03ac/replay.log`) and by #203's builds and re-check
(`evidence-repairs/03l-cleanup1/`); each line of `replay.log` is the newest check of its module,
and the Lean files at the pin equal #203's head. The rule-10 seal of #203 (8 consumer files, with controls) and lint with check 8/8b are in `evidence-repairs/03l-cleanup1/` (in the bundle).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row (or row group): `<row>: fixed / recorded / scheduled / not resolved —
<reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03l-findings.md =====

# Gate 03l — external statement-audit findings

**Verdict: DO NOT CLOSE on the supplied evidence — 0 blockers, 1 major, 3 minors.** No incorrect executable definition or theorem statement was identified in the six audited files. The major is the missing axiom-dependency evidence, not an allegation that an admitted loop lemma is actually used.

Audited head: `a3c5fa8b72e50939822f22364647dc844a3914a0`. The attached bundle has 16 sections and SHA-256 `d43f8e31da205a0f7aa1a48beb7464f929fe622b11a2944cb5033f68376b5f14`. Findings 1–4 require changes; subsequent note rows record source comparison, the specific questions, adversarial checks, and individual declaration coverage.

Scope: definitions, statements, docstrings and construction sketches. The 35 public definitions/abbreviations were first read with declaration comments removed and restated independently; all 90 public theorem/lemma statements were compared with their prose. The 16 private definitions/control types and 51 private theorem/lemma statements are also accounted for below; the four private finiteness/equality instances are implementation plumbing. Tactic correctness was not audited, and no Lean replay or new kernel axiom prints were performed. The supplied replay remains a maintainer execution claim.

Unless a repository path is written explicitly, a Lean filename below is relative to `TCSlib/Complexity/Randomized/Build/`. Line numbers are within the extracted source file, not within the concatenated bundle. Source page references use book page = PDF page − 12.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `03l-pack.md` · attestations 2 / specific question 3; `evidence/l/axioms.log` | The required axiom-dependency attestation is empty, so the current packet does not certify the advertised admission status. | The log contains only its heading: zero declaration results. “0 depend on sorryAx” is a count over an empty selection, not a clean result for the constructions. The 26-module replay reports 17 admissions in imported modules; zero local sorry declarations does not settle transitive dependencies. The older run-3 summary is historical evidence, not a printout at the audited head. Source inspection described below finds no dependency on the five Loop admissions, but is not a new kernel axiom print. | At the pinned head, include actual #print axioms output for `exists_pairSplitTM`, `exists_unaryMulTM`, `IterateFind.clean_install`, `clean_emit`, `polyTimeComputable_find`, and the seven consuming repetition theorems. Select the consuming headlines even though their declarations live outside these six files. Report every nonstandard axiom, or obtain explicit acknowledgment of any remaining debt before closure. |
| 2 | minor | `briefs/pass-shelat/DESIGN.md:381` · §2.6 steps 1–3 | The frozen construction sketch uses the wrong length guard and therefore falsely claims invariant preservation; the audited implementation has the correct guard. | Take `R = const 0`, `P = var`, `g s = true :: s`, `x = []` and `w = pairEncode [] []`. The headline orbit hypothesis holds, since only index zero is required. The design tests the old length: 0 ≤ 0, then installs a state of length 1 > 0, violating its invariant. `IterateFind.step` tests the new length 1 ≤ 0 and correctly stays. The design also describes direct exit redirection, whereas the delivered host first adds a release flag and stops one step after the positive exit. | Synchronize §2.6 with the new-output guard and the release-flag host in the two audited IterateFind files; explicitly retain the well-formed pair invariant used for the machine length bound. No executable statement needs changing. |
| 3 | minor | `IterateFind.lean`, `IterateFindHost.lean`, `StateLoop.lean`, `StringLoops.lean` · public definition APIs | Thirty-two public definitions/abbreviations lack the reading lemmas required by policy §1. | There are 35 public definitions/abbreviations. `orbit` has its zero/successor equations, and `copyTM`/`hostTM` have run/control contracts. The other 32 have no defining equation, exhaustive case equations, or predicate characterization: examples are `step`, `Clean`, `HostState`, `hostEntry`, `hostRet`, `gstep`, `gstepBound` and the string-loop data. A polynomial-time theorem or an identity restricted to reachable orbit states does not characterize a total definition on every input. This is an API defect, not a counterexample to their meanings. | Publish `Clean_iff` and the appropriate equations/cases for the remaining non-machine definitions, without adding simp attributes by default. An alternative is to make genuinely internal helpers private when that is compatible with their consumers. |
| 4 | minor | `StateLoop.lean:342,346`; `StringLoops.lean:87,91,95,196,200,204,208,452,456,460`; `IterateFindHost.lean:646` · public theorem docstrings | Thirteen public theorem docstrings give value or purpose labels instead of stating the asserted property. | Twelve projection/test docstrings omit polynomial-time computability: for example, `EmitLoop.point_poly` says “The orbit point of the state word”, and `BlockLoop.param_poly` says “The unary parameter fst z of the state word”, although their propositions assert `PolyTimeComputable`. `host_clean` says only to specialize a clean module to a call site; it omits the positive bounded call, endpoint and anchor exclusion. The formal statements are correct, but these labels do not meet policy §2’s statement-prose requirement. | State the computability assertion for the projections/tests, and the bounded host-call contract for `host_clean`. For `param_poly`, make clear that an arbitrary first component supplies the parameter through its length. |
| 5 | note | Source comparison · [PS10] §2.1, book pp. 21–24 / PDF pp. 33–36 | The deterministic infrastructure is faithful to the source machine model and supplies total, worst-case polynomial-time functions. | The source defines deterministic computation on every bit string and randomized running time for every coin tape. These machines implement deterministic functions of an explicit encoded input. Their C(n+1)^c bounds, including empty input, are the declared normalization of the source’s asymptotic polynomial convention. The source does not give the parser, tape-cleaning, or host construction being implemented here; those are formalization infrastructure, not a competing textbook proof. | No change required. |
| 6 | note | Source comparison · `PairSplit.lean` / `UnaryMul.lean` sketches | The sketches implement their complete stated functions, including rejection before any output on malformed encodings. | PairSplit uses one buffer tape rather than the two-tape estimate in DESIGN §2.4; the buffered prefix suffices to count the cut. UnaryMul stores the first component and replays its length for each symbol of the second, the expressly declared exchange of roles. For lengths a and b, its valid-input cost is 2a+2+(a+1)+b(2a+3)+1 = 2ab+3a+3b+4; with n=2a+2+b this is bounded by n²+3n+5 ≤ 5(n+1)². Neither construction needs the repetition theorem. | No change required. |
| 7 | note | Source comparison · `IterateFind.polyTimeComputable_find`; [PS10] book pp. 38–39 / PDF pp. 50–51 | The first-success semantics fit the repetition following Algorithm 38.5, with an explicit indexing convention. | The book repeats a trial and returns its first successful output. The formal theorem tests orbit indices 0 through R, so it tests R+1 states after at most R mathematical advances. A consumer making T trials can use a nonaccepting initial state and T advances, or place the first trial in the initial state and use T−1 advances when T>0. The machine’s last rejected round may execute one further guarded step before exhaustion; its result is not tested or returned, and the per-round budget already pays for it. Empty payload and exhaustion both return []; consumers requiring distinct outcomes must tag successful payloads. | No change required. |
| 8 | note | `IterateFind.lean:243,301` · polynomial budget | Polynomially many calls on polynomially bounded states have the claimed polynomial bound; there is no repeated-exponent blow-up. | Writing n for input length, the state length is at most 2n+2+P(n), and a verdict word adds 4. Thus every request length plus one is at most 2n+7+P(n). Each fixed module has cost at most its constant times this quantity to its fixed degree. The construction takes a common A,D and T(n)=A(2n+7+P(n))^D. If P(n)≤CP(n+1)^cP and R(n)≤CR(n+1)^cR, then 2n+7+P(n)≤(CP+7)(n+1)^(cP+1), and consequently c(T(n)+1)(R(n)+2)≤c(A(CP+7)^D+1)(CR+2)(n+1)^((cP+1)D+cR), exactly `final_bound`. Payload length and unary fuel generation are included in module costs. | No change required. |
| 9 | note | Coin splitting / fresh-coin use · inventory R3, R5 | The deterministic interfaces support fresh coins but do not themselves assert a probability law. | For fixed block lengths k₁,…,kₜ and a uniformly random string of length Σkᵢ, any prescribed tuple of blocks has probability 2^(−Σkᵢ)=∏ᵢ2^(−kᵢ); hence the blocks are independent and uniform. PairSplit realizes each cut, and the loop can retain the unused suffix, input and fixed advice in its state. Polynomially many blocks of polynomial length give a polynomial orbit bound. Reusing the same block would not create fresh coins; that is a caller error, not a claim of these lemmas. With zero coin length the coin space is the singleton empty string, so the deterministic special case remains nonvacuous. | No change required. |
| 10 | note | Imported dependency check · pinned `TuringMachine/Build/Loop.lean` | The audited constructions do not use the five admitted Loop interfaces on the source dependency paths examined. | At the exact audited commit, the five admitted names are `loopHostTM_contracts`, `loopHostTM_decides`, `loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget` and `emitLoopTM_computes`. `exists_loopFindTM` instead calls the earlier proved private `loopHost_contracts` and `loop_find_run`. The clean-call interfaces use `emCall_first`/`emCall_complete`. Two of the admitted names are referenced by named split-search wrappers in Build/Primitives, but those wrappers have no consumers in this pack’s source closure. The fuel path uses `computesFunInTime_lengthBits` via `timeConstructible_id`. This answers the specific source-dependency question; finding 1 still requires executable axiom evidence. | No change required. |
| 11 | note | Exact context used for the preceding check | Additional repository reads were pinned to the audited commit, not to a moving branch. | [Loop.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/a3c5fa8b72e50939822f22364647dc844a3914a0/TCSlib/Complexity/TuringMachine/Build/Loop.lean#L2714), [Build/Primitives.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/a3c5fa8b72e50939822f22364647dc844a3914a0/TCSlib/Complexity/TuringMachine/Build/Primitives.lean#L2348), and [Repetition.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/a3c5fa8b72e50939822f22364647dc844a3914a0/TCSlib/Complexity/Randomized/Repetition.lean#L216), together with the other imported files listed by replay.log, were used only as context. The current pack-a axiom-log path was unavailable at that commit; no missing output has been inferred or invented. | No change required. |
| 12 | note | Inventory · `inventory-ch2.md` §5, R1–R9 / Claim-26.3 | The in-scope constructions supply the required deterministic parts of the closure calculus. | R1/R2: the FP toolkit, pairing and state retention support pre/post-processing; the complete NUPPT closure layer is outside scope. R3: PairSplit supplies the cut, with independence as explained above. R4: advice pass-through is outside scope. R5: the first-hit loop has the required totality and polynomial bound. R6: EmitLoop accumulates ordered emissions, and BlockLoop supplies exactly the full input blocks. R7: the universal machine is outside scope. R8: EqLoop supplies full string equality, not just prefix equality. R9: arithmetic/primality hypotheses are outside scope. No inventory row directly locates a numbered source theorem in these six Build files; Claim-26.3 locates their consumers in Closure/Repetition. Rem-24.2 remains deferred: a deterministic majority routine is not a proof of Chernoff amplification. | No change required. |
| 13 | note | Internal audit record / panel repairs | The relevant loop repairs are present in the implementation; unrelated run-3 findings are not reopened. | The machine invariant asserts an actual encoded pair, the guard checks the proposed new state, the anchor lies in a disjoint host-control summand, clean calls have a genuine tape zero, and exact fuel is generated rather than a larger search bound. These address the relevant recorded loop concerns. The run-3 P2–P11 repairs concern files outside this pack; their historical success is not treated as a fresh audit of those files. | No change required. |
| 14 | note | Adversarial instantiation 1 · zero fuel and empty input | The repetition statement is nonvacuous and its zero-fuel behavior is correct. | Choose `g=id`, `P=var`, `R=const 0`. Then every required orbit length is exactly the input length. With `acc=false` the result is []; with `acc=true` and `out s=true::s` the result is true::x, including [true] at x=[]. Thus zero fuel still tests index zero and does not force an empty result. | No change required. |
| 15 | note | Adversarial instantiation 2 · the final admissible index | The last orbit point is included without requiring an extra orbit-bound hypothesis. | Let g toggle the first bit of a nonempty word and fix []; let P=var, R=const 1, x=[false], acc inspect the first bit with false default, and out=id. The tested indices are 0,1; rejection at 0 and acceptance at 1 return [true]. With R=0 the same input returns []. All orbit lengths are preserved. | No change required. |
| 16 | note | Adversarial instantiation 3 · `Clean` and equal entry/exit | Positive tape count and positive execution time rule out the usual degenerate-module loopholes. | A one-work-tape, one-state machine whose sole action halts without changing anything satisfies `Clean M id (fun _ => []) (fun _ => 1)` for every native input and argument. A zero-tape version fails the explicit 0<M.k conjunct. For a callable one-state stationary self-loop with entry=exit, the first positive exit is at time 1; stopTM first raises its release flag, then halts silently at time 2. It does not stop prematurely at time zero. | No change required. |
| 17 | note | Adversarial instantiation 4 · malformed and undersized primitive inputs | Malformed inputs and saturated cuts agree with the total specifications. | Empty input, [true,false], and a doubled prefix without a separator decode to none and both primitive outputs are []. The valid encoding pairEncode [] [] is [false,true]: PairSplit returns [false,true], while UnaryMul returns []. For u=[false,false,false], b=[true], PairSplit returns pairEncode [true] [] and UnaryMul returns three true bits. Contents of unary-count operands are deliberately irrelevant; their lengths are what is multiplied. | No change required. |
| 18 | note | Adversarial instantiation 5 · string-loop boundaries | The strict-majority, truncated-XOR and full-equality conventions are internally consistent. | MajLoop returns [false] on [] and on [true,false]. On the pair a=[true], b=[true,false], XorLoop returns [false] after one round, whereas EqLoop returns [false] because the second remainder is nonempty. A mismatch flag remains set after later equal bits. None of these interfaces silently assumes equal input lengths. | No change required. |
| 19 | note | Adversarial instantiation 6 · zero block length and a partial final block | BlockLoop stops before executing a zero-size or partial block. | Take b=const 0 and g([])=[true]. Natural division gives rounds=0, acc is true immediately, and the output is [], not a phantom g([]) chunk. For block length 2 and second component [true,false,true], exactly g([true,false]) is emitted; the final one-bit suffix is discarded. The statements consistently promise full blocks only. | No change required. |
| 20 | note | Adversarial instantiation 7 · malformed state words | The strengthened machine invariant is necessary, and the arbitrary-word state-loop bound is not vacuous. | For x=[] and P=var, arbitrarily long words consisting only of true bits have default projections [] and []; they satisfy the older projection-only LoopInv but are not encodings of a pair and have no length bound in terms of x. The audited private Inv rejects them. Separately, StateLoop.gstep_iterate_cases permits an arbitrary original word to remain unchanged, and its bound includes that original word’s length; it does not incorrectly bound malformed words by their decoded components. | No change required. |
| 21 | note | Adversarial instantiation 8 · false old-guard repair | The frozen-design invariant claim is refuted by an instance satisfying the headline orbit hypothesis. | The R=0, P=var, g=true::· example in finding 2 is the counterexample. The actual new-output guard passes this test; the defect is confined to the design sketch. | No change required. |
| 22 | note | Independent finite semantic checks | No discrepancy was found in the tested finite instances. | Independent Python transcriptions of the two primitive transition tables checked all 8,191 bit strings of length at most 12 against both the output specification and the stated time bound. Pure loop equations and stopping/output behavior were checked on all 255 raw strings of length at most 7; the block checks covered 3,825 combinations, including zero-length blocks and empty/nonempty g([]). These are finite sanity checks, not Lean executions or substitutes for the universal statements. | No change required. |
| 23 | note | `PairSplit.lean:76` · `Turing.FinTM.SplitControl` | Private supporting inductive: The control type has three parser states, rewind, copy, two remembered-bit duplication states, separator and tail: nine states in six modes. | The formal meaning agrees with the docstring. | No semantic change required. |
| 24 | note | `PairSplit.lean:96` · `Turing.FinTM.pairSplitTM` | Private supporting def: A one-work-tape buffered parser validates the pair before emitting, then doubles the requested prefix, emits the separator and copies the suffix. | The formal meaning agrees with the docstring. | No semantic change required. |
| 25 | note | `PairSplit.lean:129` · `Turing.FinTM.splitCfg` | Private supporting def: Represent the native input at index i+1, a specified buffer at work-tape origin, work head z, control q and supplied output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 26 | note | `PairSplit.lean:134` · `Turing.FinTM.splitCfg_read` | Private supporting lemma: The indexed configuration reads exactly the optional ith input entry. | The formal meaning agrees with the docstring. | No semantic change required. |
| 27 | note | `PairSplit.lean:146` · `Turing.FinTM.splitCfg_congr` | Private supporting lemma: Equal numerical input indices yield equal configurations despite different bound proofs. | The formal meaning agrees with the docstring. | No semantic change required. |
| 28 | note | `PairSplit.lean:154` · `Turing.FinTM.split_dbl_append` | Private supporting lemma: Doubling a word extended by c appends two copies of c to the doubled original word. | The formal meaning agrees with the docstring. | No semantic change required. |
| 29 | note | `PairSplit.lean:159` · `Turing.FinTM.split_first` | Private supporting lemma: Reading the first bit of an aligned block advances the input, remembers the bit, and preserves the buffer and empty output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 30 | note | `PairSplit.lean:180` · `Turing.FinTM.split_block` | Private supporting lemma: Equal two-bit blocks append their decoded bit; 10 halts silently; 01 enters rewind with the work head on the preceding cell. | The formal meaning agrees with the docstring. | No semantic change required. |
| 31 | note | `PairSplit.lean:209` · `Turing.FinTM.split_rewind` | Private supporting lemma: From work position j−1 with j at most the buffer length, j+1 steps reach position zero in copy mode. | The formal meaning agrees with the docstring. | No semantic change required. |
| 32 | note | `PairSplit.lean:244` · `Turing.FinTM.split_copy` | Private supporting lemma: For j within both available lengths, 2j steps double precisely the first j unread bits and advance both heads by j. | The formal meaning agrees with the docstring. | No semantic change required. |
| 33 | note | `PairSplit.lean:297` · `Turing.FinTM.split_sep` | Private supporting lemma: If either the buffer or input is exhausted, two stationary transitions append 01 and enter tail mode. | The formal meaning agrees with the docstring. | No semantic change required. |
| 34 | note | `PairSplit.lean:332` · `Turing.FinTM.split_tail` | Private supporting lemma: In length(rest)+1 steps, tail mode appends the entire remaining input and halts. | The formal meaning agrees with the docstring. | No semantic change required. |
| 35 | note | `PairSplit.lean:376` · `Turing.FinTM.split_finish` | Private supporting lemma: From a validated separator, at most 2·length(buffer)+length(rest)+4 steps produce the encoded saturated split and halt. | The formal meaning agrees with the docstring. | No semantic change required. |
| 36 | note | `PairSplit.lean:428` · `Turing.FinTM.split_run` | Private supporting lemma: From a parser seam, at most 3·length(rest)+2·length(buffer)+5 steps reject or split the decoded suffix at the buffer-plus-prefix length. | The formal meaning agrees with the docstring. | No semantic change required. |
| 37 | note | `PairSplit.lean:498` · `Turing.FinTM.split_computes` | Private supporting lemma: From the genuine initial configuration, the private split machine meets the advertised total function and 5(n+1) time bound. | The formal meaning agrees with the docstring. | No semantic change required. |
| 38 | note | `PairSplit.lean:531` · `Turing.FinTM.exists_pairSplitTM` | Public theorem: A finite machine computes the encoded take/drop split at the first component’s length, or [] on decode failure, in at most 5(n+1) steps. | The function, malformed-input convention and concrete time bound match the docstring. The constructive sketch and finite checks support the boundary behavior; no tactic proof audit is claimed. | No semantic change required. |
| 39 | note | `UnaryMul.lean:81` · `Turing.FinTM.MulControl` | Private supporting inductive: The control type has three parser states and back, next and emit: six states in four modes. | The formal meaning agrees with the docstring. | No semantic change required. |
| 40 | note | `UnaryMul.lean:100` · `Turing.FinTM.unaryMulTM` | Private supporting def: Buffer the first decoded component; for each symbol of the second, emit one true per buffer cell and rewind; reject malformed encodings before output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 41 | note | `UnaryMul.lean:129` · `Turing.FinTM.mulCfg` | Private supporting def: Represent the native input at index i+1, a specified buffer at work-tape origin, work head z, control q and supplied output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 42 | note | `UnaryMul.lean:134` · `Turing.FinTM.mulCfg_read` | Private supporting lemma: The indexed multiplication configuration reads exactly the optional ith input entry. | The formal meaning agrees with the docstring. | No semantic change required. |
| 43 | note | `UnaryMul.lean:146` · `Turing.FinTM.mulCfg_congr` | Private supporting lemma: Equal numerical input indices yield equal multiplication configurations despite different bound proofs. | The formal meaning agrees with the docstring. | No semantic change required. |
| 44 | note | `UnaryMul.lean:154` · `Turing.FinTM.mul_first` | Private supporting lemma: Reading the first half-block advances the input and remembers its bit without changing the buffer or emitting. | The formal meaning agrees with the docstring. | No semantic change required. |
| 45 | note | `UnaryMul.lean:175` · `Turing.FinTM.mul_block` | Private supporting lemma: Equal half-bits append a decoded buffer bit; 10 halts silently; 01 starts the rewind, all after two steps. | The formal meaning agrees with the docstring. | No semantic change required. |
| 46 | note | `UnaryMul.lean:204` · `Turing.FinTM.mul_back` | Private supporting lemma: From work position j−1, with j within the buffer, j+1 steps restore position zero in next mode and preserve output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 47 | note | `UnaryMul.lean:241` · `Turing.FinTM.mul_emit` | Private supporting lemma: From cell j with j+k equal to the buffer length, k+1 steps append k true bits and enter back mode at the buffer’s last-cell position. | The formal meaning agrees with the docstring. | No semantic change required. |
| 48 | note | `UnaryMul.lean:276` · `Turing.FinTM.mul_round` | Private supporting lemma: Consuming one remaining input symbol, emitting the buffer’s length and rewinding costs exactly 2·length(buffer)+3 steps. | The formal meaning agrees with the docstring. | No semantic change required. |
| 49 | note | `UnaryMul.lean:302` · `Turing.FinTM.mul_loop` | Private supporting lemma: For j no larger than the unread suffix length, j rounds advance the input by j and append length(buffer)·j true bits. | The formal meaning agrees with the docstring. | No semantic change required. |
| 50 | note | `UnaryMul.lean:322` · `Turing.FinTM.mul_halt` | Private supporting lemma: At the right input blank, next mode halts in one step without changing tapes, heads or output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 51 | note | `UnaryMul.lean:337` · `Turing.FinTM.mul_finish` | Private supporting lemma: From a validated separator, the rewind, suffix rounds and final halt fit length(buffer)+1+length(rest)(2·length(buffer)+3)+1 steps and emit the length product. | The formal meaning agrees with the docstring. | No semantic change required. |
| 52 | note | `UnaryMul.lean:358` · `Turing.FinTM.mul_run` | Private supporting lemma: With twice the stored buffer length at most the consumed-prefix length, the parser either rejects or produces the correct product within its stated quadratic potential. | The formal meaning agrees with the docstring. | No semantic change required. |
| 53 | note | `UnaryMul.lean:436` · `Turing.FinTM.mul_computes` | Private supporting lemma: From the genuine initial configuration, the private multiplier meets the advertised total function and 5(n+1)² time bound. | The formal meaning agrees with the docstring. | No semantic change required. |
| 54 | note | `UnaryMul.lean:473` · `Turing.FinTM.exists_unaryMulTM` | Public theorem: A finite machine outputs length(u)·length(v) true bits on a decoded pair, or [] on decode failure, in at most 5(n+1)² steps. | The function, malformed-input convention and concrete time bound match the docstring. The constructive sketch and finite checks support the boundary behavior; no tactic proof audit is claimed. | No semantic change required. |
| 55 | note | `IterateFind.lean:98` · `Complexity.IterateFind.step` | Public def: On w, compute g(snd w); install the pair of x and that value if its length is at most P(input length), otherwise retain w. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 56 | note | `IterateFind.lean:104` · `Complexity.IterateFind.Inv` | Private supporting def: Require an actual encoding of x and a state whose length is at most P(length(x)), not merely matching default projections. | The formal meaning agrees with the docstring. | No semantic change required. |
| 57 | note | `IterateFind.lean:108` · `Complexity.IterateFind.inv_init` | Private supporting theorem: The duplicated-input state is admissible whenever length(x)≤P(length(x)). | The formal meaning agrees with the docstring. | No semantic change required. |
| 58 | note | `IterateFind.lean:114` · `Complexity.IterateFind.inv_step` | Private supporting theorem: Applying the new-output-guarded step preserves the actual-pair invariant on every admissible word. | The formal meaning agrees with the docstring. | No semantic change required. |
| 59 | note | `IterateFind.lean:124` · `Complexity.IterateFind.inv_length` | Private supporting theorem: An admissible word has length at most 2·length(x)+2+P(length(x)). | The formal meaning agrees with the docstring. | No semantic change required. |
| 60 | note | `IterateFind.lean:132` · `Complexity.IterateFind.verdictWord` | Private supporting def: Prefix the current word with an encoded singleton test of its decoded state component. | The formal meaning agrees with the docstring. | No semantic change required. |
| 61 | note | `IterateFind.lean:137` · `Complexity.IterateFind.stepWord` | Private supporting def: Strip a verdict prefix, recover x from the inner word, and install the new state only if its length fits the polynomial bound. | The formal meaning agrees with the docstring. | No semantic change required. |
| 62 | note | `IterateFind.lean:143` · `Complexity.IterateFind.outWord` | Private supporting def: Apply out to the state component beneath the verdict prefix. | The formal meaning agrees with the docstring. | No semantic change required. |
| 63 | note | `IterateFind.lean:147` · `Complexity.IterateFind.verdictWord_head` | Private supporting theorem: The first bit of an encoded verdict word is precisely acc of the decoded state. | The formal meaning agrees with the docstring. | No semantic change required. |
| 64 | note | `IterateFind.lean:152` · `Complexity.IterateFind.verdictWord_length` | Private supporting theorem: Adding the encoded singleton verdict increases the word’s length by exactly four. | The formal meaning agrees with the docstring. | No semantic change required. |
| 65 | note | `IterateFind.lean:158` · `Complexity.IterateFind.stepWord_verdictWord` | Private supporting theorem: On the verdict encoding of any pair, stepWord equals the corresponding guarded step; no admissibility hypothesis is needed for this identity. | The docstring mentions an admissible pair, but the identity holds for every encoded pair. This benign strengthening is usable by the headline and has no inconsistent hypothesis. | No semantic change required. |
| 66 | note | `IterateFind.lean:164` · `Complexity.IterateFind.outWord_verdictWord` | Private supporting theorem: On the verdict encoding of a pair with state s, the payload is out(s). | The formal meaning agrees with the docstring. | No semantic change required. |
| 67 | note | `IterateFind.lean:170` · `Complexity.IterateFind.verdictWord_poly` | Private supporting theorem: Installing an encoded singleton verdict is polynomial-time whenever the singleton test is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 68 | note | `IterateFind.lean:183` · `Complexity.IterateFind.stepWord_poly` | Private supporting theorem: The guarded update beneath a verdict prefix is polynomial-time whenever g is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 69 | note | `IterateFind.lean:207` · `Complexity.IterateFind.outWord_poly` | Private supporting theorem: Extracting and mapping the payload beneath a verdict prefix is polynomial-time whenever out is. | The formal meaning agrees with the docstring. | No semantic change required. |
| 70 | note | `IterateFind.lean:212` · `Complexity.IterateFind.dupWord_poly` | Private supporting theorem: Encoding two copies of the input is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 71 | note | `IterateFind.lean:218` · `Complexity.IterateFind.request_budget` | Private supporting lemma: If d≤D and m+1≤n, then A(m+1)^d≤A n^D; the hypotheses ensure n≥1 even when exponents are zero. | The formal meaning agrees with the docstring. | No semantic change required. |
| 72 | note | `IterateFind.lean:224` · `Complexity.IterateFind.find?_congr_of_mem` | Public theorem: Agreement of two Boolean predicates on every member of a list implies identical first-find results on that list. | The formal meaning agrees with the docstring. | No semantic change required. |
| 73 | note | `IterateFind.lean:243` · `Complexity.IterateFind.final_bound` | Private supporting lemma: Polynomial majorants for P and R imply the explicit normal-form majorant of the complete loop budget stated above. | The formal meaning agrees with the docstring. | No semantic change required. |
| 74 | note | `IterateFind.lean:301` · `Complexity.IterateFind.polyTimeComputable_find` | Public theorem: Given polynomial-time step, test and payload and an orbit bound through R, the first accepted guarded-orbit payload is polynomial-time, with [] on exhaustion. | The hypotheses are realized, for example, by g=id and P=var. The guarded formulation has the advertised unguarded meaning on indices 0 through R; see the source/budget and endpoint checks above. | No semantic change required. |
| 75 | note | `IterateFindHost.lean:88` · `Complexity.IterateFind.stopTM` | Private supporting def: Add a release flag to a callable machine; after its first physical step, halt silently on reaching the designated exit, allowing entry=exit. | The formal meaning agrees with the docstring. | No semantic change required. |
| 76 | note | `IterateFindHost.lean:98` · `Complexity.IterateFind.stopCfg` | Private supporting def: Map a configuration’s optional state to the flag/state pair, preserving all tape, head and output fields. | The formal meaning agrees with the docstring. | No semantic change required. |
| 77 | note | `IterateFindHost.lean:104` · `Complexity.IterateFind.stop_step` | Private supporting lemma: Before a released exit, a live configuration takes the source machine’s physical transition and sets the flag to true. | The formal meaning agrees with the docstring. | No semantic change required. |
| 78 | note | `IterateFindHost.lean:118` · `Complexity.IterateFind.live_prefix` | Private supporting lemma: A live configuration at time t implies that every configuration at times at most t was live. | The formal meaning agrees with the docstring. | No semantic change required. |
| 79 | note | `IterateFindHost.lean:132` · `Complexity.IterateFind.stop_clean` | Private supporting lemma: A certified first-positive-exit run becomes a halting run one silent step later with every clean endpoint field and output preserved. | The formal meaning agrees with the docstring. | No semantic change required. |
| 80 | note | `IterateFindHost.lean:165` · `Complexity.IterateFind.call_first_halt` | Private supporting lemma: A run starting live and halting by t can be cut at a positive first halt no later than t with exactly the same entire endpoint. | The formal meaning agrees with the docstring. | No semantic change required. |
| 81 | note | `IterateFindHost.lean:186` · `Complexity.IterateFind.Clean` | Public def: Require a positive work-tape count and a positive first halt, uniformly over native inputs and argument words, within B(argument length), restoring the clean seam with the specified replacement and emitted word. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 82 | note | `IterateFindHost.lean:195` · `Complexity.IterateFind.clean_stop` | Private supporting lemma: A positive-tape callable clean contract becomes Clean for the release wrapper, with budget B(n)+1. | The formal meaning agrees with the docstring. | No semantic change required. |
| 83 | note | `IterateFindHost.lean:214` · `Complexity.IterateFind.bridge_bound` | Private supporting lemma: When result length is at most A(n+1)^d, the callable overhead plus the extra stop step is at most (c(2A+1)+1)(n+1)^(d+1). | The formal meaning agrees with the docstring. | No semantic change required. |
| 84 | note | `IterateFindHost.lean:235` · `Complexity.IterateFind.clean_install` | Public lemma: Every polynomial-time word map has an install module satisfying Clean with a polynomial argument-length budget and empty emission. | The formal meaning agrees with the docstring. | No semantic change required. |
| 85 | note | `IterateFindHost.lean:255` · `Complexity.IterateFind.clean_emit` | Public lemma: Every polynomial-time word map has an emit module satisfying Clean with a polynomial argument-length budget, retaining its argument and emitting the map’s value. | The formal meaning agrees with the docstring. | No semantic change required. |
| 86 | note | `IterateFindHost.lean:274` · `Complexity.IterateFind.padAction` | Private supporting def: At each target tape index below the source tape count use its original action; at other indices idle, retaining the input, output and state actions. | The formal meaning agrees with the docstring. | No semantic change required. |
| 87 | note | `IterateFindHost.lean:279` · `Complexity.IterateFind.padTM` | Private supporting def: Given enough target tapes, reinterpret a machine on that larger bank without changing its state type or original behavior. | The formal meaning agrees with the docstring. | No semantic change required. |
| 88 | note | `IterateFindHost.lean:288` · `Complexity.IterateFind.padCfg` | Private supporting def: At target indices below the source tape count retain its tapes and heads; at other indices use blank tapes and zero heads, preserving state, native-input position and output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 89 | note | `IterateFindHost.lean:295` · `Complexity.IterateFind.pad_apply` | Private supporting lemma: Applying an extended action to an extended configuration equals extending the original resulting configuration. | The formal meaning agrees with the docstring. | No semantic change required. |
| 90 | note | `IterateFindHost.lean:305` · `Complexity.IterateFind.pad_run` | Private supporting lemma: When the target bank is large enough, the padded machine follows the original run in lockstep under the configuration embedding. | The formal meaning agrees with the docstring. | No semantic change required. |
| 91 | note | `IterateFindHost.lean:323` · `Complexity.IterateFind.pad_seam` | Private supporting lemma: With a genuine source tape zero, padding a clean seam yields the corresponding target seam with the same word and output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 92 | note | `IterateFindHost.lean:343` · `Complexity.IterateFind.copyTM` | Public def: Use one tape and two states to copy the native input to tape zero, then rewind both heads and halt without emitting. | The formal meaning agrees with the docstring. | No semantic change required. |
| 93 | note | `IterateFindHost.lean:359` · `Complexity.IterateFind.copyCfg` | Private supporting def: Store the copier’s optional control, bounded native-input position, buffer at tape origin, integer work-head position and empty output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 94 | note | `IterateFindHost.lean:369` · `Complexity.IterateFind.copy_step` | Private supporting lemma: Before the input ends, one copier step appends the next input bit to the buffer and advances both heads. | The formal meaning agrees with the docstring. | No semantic change required. |
| 95 | note | `IterateFindHost.lean:397` · `Complexity.IterateFind.copy_turn` | Private supporting lemma: At the right input blank, the copier moves both heads left and enters rewind control. | The formal meaning agrees with the docstring. | No semantic change required. |
| 96 | note | `IterateFindHost.lean:425` · `Complexity.IterateFind.copy_rewind` | Private supporting lemma: From native position p≤length(x), p rewind steps reach the left blank and shift the work head left by p. | The formal meaning agrees with the docstring. | No semantic change required. |
| 97 | note | `IterateFindHost.lean:458` · `Complexity.IterateFind.copy_finish` | Private supporting lemma: At the left blank, the copier moves both heads right and halts. | The formal meaning agrees with the docstring. | No semantic change required. |
| 98 | note | `IterateFindHost.lean:484` · `Complexity.IterateFind.copy_clean` | Public lemma: From the empty seam, copying x first halts after exactly 2·length(x)+2 steps at the seam containing x and empty output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 99 | note | `IterateFindHost.lean:531` · `Complexity.IterateFind.HostState` | Public abbrev: Take a disjoint union of three host-control states with the tagged state types of five component machines. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 100 | note | `IterateFindHost.lean:534` · `Complexity.IterateFind.hostEntry` | Public def: Embed the selected component’s initial state in its tagged host summand. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 101 | note | `IterateFindHost.lean:539` · `Complexity.IterateFind.hostRet` | Public def: Send component 0 to entry 1, components 1 and 3 to the anchor, component 2 to the branch, and component 4 to the halt control. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 102 | note | `IterateFindHost.lean:547` · `Complexity.IterateFind.hostTM` | Public def: Pad five components to K+1 tapes; forward their actions and outputs to fixed returns, dispatch the anchor to verdict, branch on tape zero to payload or step, and halt at control 2. | The formal meaning agrees with the docstring. | No semantic change required. |
| 103 | note | `IterateFindHost.lean:565` · `Complexity.IterateFind.host_seam` | Private supporting lemma: Forwarding a padded seam maps live module states to their tagged summand and a halted state to its return, concatenating the output prefix. | The formal meaning agrees with the docstring. | No semantic change required. |
| 104 | note | `IterateFindHost.lean:589` · `Complexity.IterateFind.host_call` | Public lemma: A module’s live-prefix and halting-seam contract transfers to its host call, excluding the anchor before the endpoint and appending its output after any supplied prefix. | First-halt behavior is required explicitly by the live-prefix and endpoint hypotheses. Although t>0 is not written separately here, the live initial state and halted endpoint imply it. | No semantic change required. |
| 105 | note | `IterateFindHost.lean:632` · `Complexity.IterateFind.guard_add` | Public lemma: Two consecutive run segments excluding the anchor at all indices below their respective durations compose to a segment with the same exclusion. | The half-open time intervals are correct, including b=0: then no guard at the joining endpoint is needed. | No semantic change required. |
| 106 | note | `IterateFindHost.lean:646` · `Complexity.IterateFind.host_clean` | Public lemma: A Clean module supplies a positive bounded host call, with anchor exclusion, the specified installed word, and the supplied prefix followed by its emission. | The bounded positive call, endpoint, output concatenation and anchor guard fit its consumer. The docstring states only a specialization purpose, not this contract (finding 4). | Apply finding 4. |
| 107 | note | `IterateFindHost.lean:661` · `Complexity.IterateFind.host_dispatch` | Public lemma: The anchor takes one stationary step to the verdict component’s entry, preserving the clean state word. | The formal meaning agrees with the docstring. | No semantic change required. |
| 108 | note | `IterateFindHost.lean:671` · `Complexity.IterateFind.host_branch` | Public lemma: If tape zero’s first bit is b, the branch takes one stationary step to payload when b is true and to step when b is false. | The formal meaning agrees with the docstring. | No semantic change required. |
| 109 | note | `IterateFindHost.lean:686` · `Complexity.IterateFind.host_halt` | Public lemma: The halt control takes one step to state none, preserving the clean tapes and the entire existing output. | The formal meaning agrees with the docstring. | No semantic change required. |
| 110 | note | `StateLoop.lean:79` · `Complexity.StateLoop.lenLe_comp` | Public theorem: The one-bit test length(g(x))≤length(f(x)) is polynomial-time when both maps are polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 111 | note | `StateLoop.lean:88` · `Complexity.StateLoop.unaryPoly_comp` | Public theorem: If f is polynomial-time, producing p(length(f(x))) true bits is polynomial-time for every syntactic polynomial p. | The formal meaning agrees with the docstring. | No semantic change required. |
| 112 | note | `StateLoop.lean:95` · `Complexity.StateLoop.headBit_poly` | Public theorem: The first bit, with false for an empty word and packaged as a singleton output, is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 113 | note | `StateLoop.lean:105` · `Complexity.StateLoop.tail_poly` | Public theorem: Deleting the first bit, with [] on [], is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 114 | note | `StateLoop.lean:113` · `Complexity.StateLoop.cons_poly` | Public theorem: Prepending any fixed bit is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 115 | note | `StateLoop.lean:117` · `Complexity.StateLoop.isNil_poly` | Public theorem: The singleton emptiness verdict is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 116 | note | `StateLoop.lean:123` · `Complexity.StateLoop.not_poly` | Public theorem: Negating a polynomial-time singleton Boolean test preserves polynomial-time computability. | The formal meaning agrees with the docstring. | No semantic change required. |
| 117 | note | `StateLoop.lean:131` · `Complexity.StateLoop.or_poly` | Public theorem: Disjoining two polynomial-time singleton Boolean tests preserves polynomial-time computability. | The formal meaning agrees with the docstring. | No semantic change required. |
| 118 | note | `StateLoop.lean:138` · `Complexity.StateLoop.xor_poly` | Public theorem: Taking exclusive-or of two polynomial-time singleton Boolean tests preserves polynomial-time computability. | The formal meaning agrees with the docstring. | No semantic change required. |
| 119 | note | `StateLoop.lean:146` · `Complexity.StateLoop.length_pairFstD_add_pairSndD_le` | Public theorem: The sum of the lengths of both default-decoded components is at most the original word’s length, including decode failure. | The formal meaning agrees with the docstring. | No semantic change required. |
| 120 | note | `StateLoop.lean:158` · `Complexity.StateLoop.length_flatMap_range_le` | Public theorem: Concatenating i chunks, each of length at most M at indices below i, produces length at most i·M. | The statement only bounds the chunks that are actually concatenated, and also handles i=0 or M=0. | No semantic change required. |
| 121 | note | `StateLoop.lean:170` · `Complexity.StateLoop.find?_range_eq_some` | Public theorem: If N≤m, the predicate is false below N and true at N, then find over indices 0 through m returns exactly some N. | The formal meaning agrees with the docstring. | No semantic change required. |
| 122 | note | `StateLoop.lean:181` · `Complexity.StateLoop.orbit` | Public def: Start at start(x); at every successor apply step to the pair of the retained input x and the preceding state. | The formal meaning agrees with the docstring. | No semantic change required. |
| 123 | note | `StateLoop.lean:186` · `Complexity.StateLoop.orbit_zero` | Public theorem: The zeroth state is start(x). | The formal meaning agrees with the docstring. | No semantic change required. |
| 124 | note | `StateLoop.lean:190` · `Complexity.StateLoop.orbit_succ` | Public theorem: The next state is step applied to the encoded pair of x and the current state. | The formal meaning agrees with the docstring. | No semantic change required. |
| 125 | note | `StateLoop.lean:195` · `Complexity.StateLoop.gstep` | Public def: Replace w by the pair of fst(w) and step(w) exactly when the new state fits B(length(fst(w))); otherwise preserve w. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 126 | note | `StateLoop.lean:199` · `Complexity.StateLoop.gstepBound` | Public def: Return the syntactic polynomial evaluating to 3n+2+B(n). | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 127 | note | `StateLoop.lean:205` · `Complexity.StateLoop.gstep_poly` | Public theorem: Guarding a polynomial-time step by the specified polynomial length test remains polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 128 | note | `StateLoop.lean:225` · `Complexity.StateLoop.gstep_iterate_cases` | Public theorem: Every guarded iterate is either the original word or a pair with its original first projection and a second component satisfying the guard bound. | The original-word alternative is essential for malformed inputs or initially oversized states; the second alternative preserves the decoded parameter and bounds the new state. | No semantic change required. |
| 129 | note | `StateLoop.lean:249` · `Complexity.StateLoop.length_gstep_iterate_le` | Public theorem: At every iteration, from any raw starting word w, the guarded state has length at most 3·length(w)+2+B(length(w)). | The formal meaning agrees with the docstring. | No semantic change required. |
| 130 | note | `StateLoop.lean:261` · `Complexity.StateLoop.gstep_iterate_eq` | Public theorem: If genuine states through n satisfy B(length(x)), guarded iteration from the encoded initial state agrees with the genuine orbit through n. | The bound includes index zero and the last required state. It is sufficient, and does not demand bounded growth after the requested prefix. | No semantic change required. |
| 131 | note | `StateLoop.lean:280` · `Complexity.StateLoop.IterLoop.start` | Public def: Pair an empty unary counter with the input x. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 132 | note | `StateLoop.lean:284` · `Complexity.StateLoop.IterLoop.step` | Public def: From the retained-input/state pair, prepend a true token to the counter and apply g to the current point. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 133 | note | `StateLoop.lean:288` · `Complexity.StateLoop.IterLoop.acc` | Public def: Accept exactly when the counter length is at least R of the retained input’s length. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 134 | note | `StateLoop.lean:292` · `Complexity.StateLoop.IterLoop.out` | Public def: Extract the current orbit point from the nested state. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 135 | note | `StateLoop.lean:295` · `Complexity.StateLoop.IterLoop.start_poly` | Public theorem: The empty-counter initial state is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 136 | note | `StateLoop.lean:299` · `Complexity.StateLoop.IterLoop.step_poly` | Public theorem: Advancing the point and counter is polynomial-time when g is. | The formal meaning agrees with the docstring. | No semantic change required. |
| 137 | note | `StateLoop.lean:305` · `Complexity.StateLoop.IterLoop.acc_poly` | Public theorem: The counter-threshold singleton test is polynomial-time for every R. | The formal meaning agrees with the docstring. | No semantic change required. |
| 138 | note | `StateLoop.lean:312` · `Complexity.StateLoop.IterLoop.out_poly` | Public theorem: Extracting the current point is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 139 | note | `StateLoop.lean:316` · `Complexity.StateLoop.IterLoop.orbit_eq` | Public theorem: After i rounds the state is the encoded pair of i true tokens and the i-fold iterate of g on x. | The formal meaning agrees with the docstring. | No semantic change required. |
| 140 | note | `StateLoop.lean:329` · `Complexity.StateLoop.EmitLoop.start` | Public def: Initialize an empty counter, point x and empty accumulator. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 141 | note | `StateLoop.lean:332` · `Complexity.StateLoop.EmitLoop.step` | Public def: Increment the counter, advance the point by g, and append emit of the old point to the accumulator. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 142 | note | `StateLoop.lean:338` · `Complexity.StateLoop.EmitLoop.out` | Public def: Return the accumulator followed by emit of the current point. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 143 | note | `StateLoop.lean:342` · `Complexity.StateLoop.EmitLoop.point_poly` | Public theorem: Extracting the current point from the retained-input/state word is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 144 | note | `StateLoop.lean:346` · `Complexity.StateLoop.EmitLoop.accum_poly` | Public theorem: Extracting the accumulator from the retained-input/state word is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 145 | note | `StateLoop.lean:350` · `Complexity.StateLoop.EmitLoop.start_poly` | Public theorem: Initializing the counter, point and accumulator is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 146 | note | `StateLoop.lean:355` · `Complexity.StateLoop.EmitLoop.step_poly` | Public theorem: The accumulating step is polynomial-time when g and emit are. | The formal meaning agrees with the docstring. | No semantic change required. |
| 147 | note | `StateLoop.lean:361` · `Complexity.StateLoop.EmitLoop.out_poly` | Public theorem: Appending the final point’s emission to the accumulator is polynomial-time when emit is. | The formal meaning agrees with the docstring. | No semantic change required. |
| 148 | note | `StateLoop.lean:366` · `Complexity.StateLoop.EmitLoop.orbit_eq` | Public theorem: After i rounds the counter is i, the point is g iterated i times on x, and the accumulator concatenates emissions from indices 0 through i−1. | The formal meaning agrees with the docstring. | No semantic change required. |
| 149 | note | `StringLoops.lean:68` · `Complexity.StateLoop.MajLoop.start` | Public def: Store the entire word as the remainder and initialize both unary count strings to empty. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 150 | note | `StringLoops.lean:72` · `Complexity.StateLoop.MajLoop.step` | Public def: Drop the remainder’s first bit and add a true token to its selected count string; an empty remainder has false default. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 151 | note | `StringLoops.lean:79` · `Complexity.StateLoop.MajLoop.acc` | Public def: Accept exactly when the remaining word is empty. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 152 | note | `StringLoops.lean:82` · `Complexity.StateLoop.MajLoop.out` | Public def: Output the singleton test false-count+1≤true-count, so ties return false. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 153 | note | `StringLoops.lean:87` · `Complexity.StateLoop.MajLoop.rest_poly` | Public theorem: The projection extracting the remaining word is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 154 | note | `StringLoops.lean:91` · `Complexity.StateLoop.MajLoop.trues_poly` | Public theorem: The projection extracting the true-count string is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 155 | note | `StringLoops.lean:95` · `Complexity.StateLoop.MajLoop.falses_poly` | Public theorem: The projection extracting the false-count string is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 156 | note | `StringLoops.lean:99` · `Complexity.StateLoop.MajLoop.start_poly` | Public theorem: Initializing the majority-loop state is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 157 | note | `StringLoops.lean:103` · `Complexity.StateLoop.MajLoop.step_poly` | Public theorem: Consuming one bit and updating its count is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 158 | note | `StringLoops.lean:112` · `Complexity.StateLoop.MajLoop.acc_poly` | Public theorem: Testing whether the remaining input is empty is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 159 | note | `StringLoops.lean:116` · `Complexity.StateLoop.MajLoop.out_poly` | Public theorem: Comparing the two unary counts for strict majority is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 160 | note | `StringLoops.lean:121` · `Complexity.StateLoop.MajLoop.orbit_eq` | Public theorem: Through the input length, the remainder is the suffix after i bits and the two counters count the true and false bits of the first i bits. | The formal meaning agrees with the docstring. | No semantic change required. |
| 161 | note | `StringLoops.lean:137` · `Complexity.StateLoop.MajLoop.orbit_length_le` | Public theorem: Every state through the stopping round has length at most 5·length(w)+4. | The formal meaning agrees with the docstring. | No semantic change required. |
| 162 | note | `StringLoops.lean:147` · `Complexity.StateLoop.MajLoop.acc_orbit_false` | Public theorem: At every index strictly below length(w), the encoded genuine state is rejected because a bit remains. | The formal meaning agrees with the docstring. | No semantic change required. |
| 163 | note | `StringLoops.lean:153` · `Complexity.StateLoop.MajLoop.acc_orbit_true` | Public theorem: At index length(w), the encoded genuine state is accepted. | The formal meaning agrees with the docstring. | No semantic change required. |
| 164 | note | `StringLoops.lean:159` · `Complexity.StateLoop.MajLoop.out_orbit` | Public theorem: At the stopping round, the returned bit is exactly the strict-majority test length(w)<2·count_true(w). | The formal meaning agrees with the docstring. | No semantic change required. |
| 165 | note | `StringLoops.lean:175` · `Complexity.StateLoop.XorLoop.start` | Public def: Initialize the two decoded components as remainders and an empty output accumulator. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 166 | note | `StringLoops.lean:178` · `Complexity.StateLoop.XorLoop.step` | Public def: Drop one bit from each remainder and append their head-bit XOR, using false defaults on empty remainders. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 167 | note | `StringLoops.lean:186` · `Complexity.StateLoop.XorLoop.acc` | Public def: Accept as soon as either remaining component is empty. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 168 | note | `StringLoops.lean:190` · `Complexity.StateLoop.XorLoop.out` | Public def: Extract the accumulated XOR word. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 169 | note | `StringLoops.lean:193` · `Complexity.StateLoop.XorLoop.rounds` | Public def: Take the minimum of the two decoded component lengths. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 170 | note | `StringLoops.lean:196` · `Complexity.StateLoop.XorLoop.fstRest_poly` | Public theorem: Extracting the first remainder is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 171 | note | `StringLoops.lean:200` · `Complexity.StateLoop.XorLoop.sndRest_poly` | Public theorem: Extracting the second remainder is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 172 | note | `StringLoops.lean:204` · `Complexity.StateLoop.XorLoop.accum_poly` | Public theorem: Extracting the accumulator is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 173 | note | `StringLoops.lean:208` · `Complexity.StateLoop.XorLoop.xorBit_poly` | Public theorem: Computing the singleton XOR of the two defaulted head bits is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 174 | note | `StringLoops.lean:217` · `Complexity.StateLoop.XorLoop.start_poly` | Public theorem: Initializing the two remainders and accumulator is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 175 | note | `StringLoops.lean:222` · `Complexity.StateLoop.XorLoop.step_poly` | Public theorem: Consuming the heads and appending their XOR is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 176 | note | `StringLoops.lean:227` · `Complexity.StateLoop.XorLoop.acc_poly` | Public theorem: Testing whether either remainder is empty is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 177 | note | `StringLoops.lean:235` · `Complexity.StateLoop.XorLoop.out_poly` | Public theorem: Returning the XOR accumulator is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 178 | note | `StringLoops.lean:239` · `Complexity.StateLoop.XorLoop.orbit_eq` | Public theorem: Through the minimum length, both remainders are dropped by i and the accumulator is the first i bits of the zipWith-XOR result. | The formal meaning agrees with the docstring. | No semantic change required. |
| 179 | note | `StringLoops.lean:257` · `Complexity.StateLoop.XorLoop.orbit_length_le` | Public theorem: Every state through the stopping round has length at most 5·length(z)+4. | The formal meaning agrees with the docstring. | No semantic change required. |
| 180 | note | `StringLoops.lean:265` · `Complexity.StateLoop.XorLoop.acc_orbit_false` | Public theorem: Before the minimum-length round both remainders are nonempty, so the acceptance test is false. | The formal meaning agrees with the docstring. | No semantic change required. |
| 181 | note | `StringLoops.lean:274` · `Complexity.StateLoop.XorLoop.acc_orbit_true` | Public theorem: At the minimum-length round one remainder is empty, so the acceptance test is true. | The formal meaning agrees with the docstring. | No semantic change required. |
| 182 | note | `StringLoops.lean:281` · `Complexity.StateLoop.XorLoop.out_orbit` | Public theorem: The final output is precisely zipWith xor of the decoded components, truncated to their shorter length. | The formal meaning agrees with the docstring. | No semantic change required. |
| 183 | note | `StringLoops.lean:298` · `Complexity.StateLoop.EqLoop.step` | Public def: Consume both heads and set the mismatch flag to [true] if they differ; otherwise preserve the previous flag. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 184 | note | `StringLoops.lean:306` · `Complexity.StateLoop.EqLoop.out` | Public def: Output true exactly when both remainders and the mismatch flag are empty. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 185 | note | `StringLoops.lean:311` · `Complexity.StateLoop.EqLoop.flag` | Public def: Return [] when the two length-i prefixes agree and [true] otherwise. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 186 | note | `StringLoops.lean:314` · `Complexity.StateLoop.EqLoop.step_poly` | Public theorem: Updating the remainders and mismatch flag is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 187 | note | `StringLoops.lean:321` · `Complexity.StateLoop.EqLoop.out_poly` | Public theorem: Computing the final equality verdict from both remainders and the flag is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 188 | note | `StringLoops.lean:331` · `Complexity.StateLoop.EqLoop.append_singleton_eq_iff` | Public theorem: Two lists extended by one bit are equal exactly when both their original lists and their last bits agree. | The formal meaning agrees with the docstring. | No semantic change required. |
| 189 | note | `StringLoops.lean:340` · `Complexity.StateLoop.EqLoop.flag_succ` | Public theorem: When both ith bits exist, the next mismatch flag is [true] if they differ and otherwise equals the old flag. | The two optional-index hypotheses ensure both next bits exist; the prefix-equivalence update then matches the docstring and is satisfiable. | No semantic change required. |
| 190 | note | `StringLoops.lean:348` · `Complexity.StateLoop.EqLoop.length_flag_le` | Public theorem: The mismatch flag always has length at most one. | The formal meaning agrees with the docstring. | No semantic change required. |
| 191 | note | `StringLoops.lean:354` · `Complexity.StateLoop.EqLoop.orbit_eq` | Public theorem: Through the shorter length, the remainders are the corresponding suffixes and the flag records equality of the consumed prefixes. | The formal meaning agrees with the docstring. | No semantic change required. |
| 192 | note | `StringLoops.lean:369` · `Complexity.StateLoop.EqLoop.orbit_length_le` | Public theorem: Every equality-loop state through the stopping round has length at most 5·length(z)+5. | The formal meaning agrees with the docstring. | No semantic change required. |
| 193 | note | `StringLoops.lean:378` · `Complexity.StateLoop.EqLoop.acc_orbit_false` | Public theorem: The reused XorLoop stopping test is false before the shorter input has been consumed. | The formal meaning agrees with the docstring. | No semantic change required. |
| 194 | note | `StringLoops.lean:387` · `Complexity.StateLoop.EqLoop.acc_orbit_true` | Public theorem: The reused stopping test is true when the shorter input has been consumed. | The formal meaning agrees with the docstring. | No semantic change required. |
| 195 | note | `StringLoops.lean:395` · `Complexity.StateLoop.EqLoop.verdict_eq` | Public theorem: At the minimum-length cutoff, emptiness of both remainders and an unset prefix flag is equivalent to equality of the entire two strings. | The formal meaning agrees with the docstring. | No semantic change required. |
| 196 | note | `StringLoops.lean:416` · `Complexity.StateLoop.EqLoop.out_orbit` | Public theorem: The final singleton output is exactly the equality test of the two decoded components. | The formal meaning agrees with the docstring. | No semantic change required. |
| 197 | note | `StringLoops.lean:430` · `Complexity.StateLoop.BlockLoop.start` | Public def: Store the decoded second component as the remainder and initialize an empty accumulator. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 198 | note | `StringLoops.lean:433` · `Complexity.StateLoop.BlockLoop.blk` | Public def: Evaluate b at the length of the first component of the retained original input. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 199 | note | `StringLoops.lean:436` · `Complexity.StateLoop.BlockLoop.step` | Public def: Drop one block from the remainder and append g of that block’s prefix to the accumulator. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 200 | note | `StringLoops.lean:441` · `Complexity.StateLoop.BlockLoop.acc` | Public def: Accept when fewer than one block’s bits remain, or when the block length is zero. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 201 | note | `StringLoops.lean:445` · `Complexity.StateLoop.BlockLoop.out` | Public def: Return the accumulator. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 202 | note | `StringLoops.lean:448` · `Complexity.StateLoop.BlockLoop.rounds` | Public def: Divide the second component’s length by b of the first component’s length, with natural division by zero giving zero. | The formal meaning agrees with the docstring. Its required general reading equation/characterization is missing (finding 3). | Apply finding 3. |
| 203 | note | `StringLoops.lean:452` · `Complexity.StateLoop.BlockLoop.param_poly` | Public theorem: Extracting the first component of the retained input is polynomial-time; its bit contents need not be unary. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 204 | note | `StringLoops.lean:456` · `Complexity.StateLoop.BlockLoop.rest_poly` | Public theorem: Extracting the remaining data is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 205 | note | `StringLoops.lean:460` · `Complexity.StateLoop.BlockLoop.accum_poly` | Public theorem: Extracting the accumulated output is polynomial-time. | The formal statement has the stated computability meaning; its docstring omits the computability assertion (finding 4). | Apply finding 4. |
| 206 | note | `StringLoops.lean:464` · `Complexity.StateLoop.BlockLoop.start_poly` | Public theorem: Initializing the remainder and accumulator is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 207 | note | `StringLoops.lean:469` · `Complexity.StateLoop.BlockLoop.step_poly` | Public theorem: Cutting a polynomially specified block, applying polynomial-time g and appending its result is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 208 | note | `StringLoops.lean:482` · `Complexity.StateLoop.BlockLoop.acc_poly` | Public theorem: Testing for a short remainder or zero block length is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 209 | note | `StringLoops.lean:494` · `Complexity.StateLoop.BlockLoop.out_poly` | Public theorem: Returning the accumulator is polynomial-time. | The formal meaning agrees with the docstring. | No semantic change required. |
| 210 | note | `StringLoops.lean:498` · `Complexity.StateLoop.BlockLoop.orbit_eq` | Public theorem: At every i, the remainder is the original suffix after i block lengths and the accumulator concatenates g of the first i block prefixes. | The formula is valid even after termination, where the pure step can append g([]); termination theorems only consume indices through rounds, so this stronger all-round formula causes no extra output. | No semantic change required. |
| 211 | note | `StringLoops.lean:521` · `Complexity.StateLoop.BlockLoop.orbit_length_le` | Public theorem: Given length(g(y))≤C(length(y)+1)^c, states through the full-block count have length at most 2·length(z)+2+length(z)·C(b(length(z))+1)^c. | The formal meaning agrees with the docstring. | No semantic change required. |
| 212 | note | `StringLoops.lean:546` · `Complexity.StateLoop.BlockLoop.acc_orbit_false` | Public theorem: Before the full-block count is reached the block size is positive and a whole block remains, so the stopping test is false. | The strict-index hypothesis is intentionally impossible when the block size is zero; the endpoint theorem then handles immediate termination. This local empty-range case does not trivialize the construction. | No semantic change required. |
| 213 | note | `StringLoops.lean:562` · `Complexity.StateLoop.BlockLoop.acc_orbit_true` | Public theorem: At the full-block count the remainder is shorter than the block size, or that size is zero, so the stopping test is true. | The formal meaning agrees with the docstring. | No semantic change required. |
| 214 | note | `StringLoops.lean:577` · `Complexity.StateLoop.BlockLoop.out_orbit` | Public theorem: At termination the output is exactly the ordered concatenation of g over the original full blocks. | The formal meaning agrees with the docstring. | No semantic change required. |


Notation: `FP` means polynomial-time computable string functions; `fst`/`snd` mean the imported default-empty pair projections. In the budget row, n is input length; P and R are the supplied orbit/fuel polynomials; A,D bound the fixed module costs; CP,cP and CR,cR are their displayed polynomial-majorant constants; c is the loop-combinator coefficient. In the primitive cost calculation, a and b are the two component lengths. In the fresh-coin calculation, t is the number of calls and kᵢ is the fixed length of block i. No distributional conclusion is asserted for malformed or undersized coin inputs.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
