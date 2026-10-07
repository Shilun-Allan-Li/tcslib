Independent adversarial audit — Arora–Barak Chapter 1, epoch-1 fill round

Audited commit: [`d3393b35764710ff3d7ae538d5133284291d9ef4`](https://github.com/Shilun-Allan-Li/tcslib/commit/d3393b35764710ff3d7ae538d5133284291d9ef4), compared with `9f735248212c1d1d842b299b431b2b680220ac5b`, on `complexity/arora-barak-ch1`. Inputs: the uploaded `epoch1-bundle.md` and Arora–Barak (2009), §§1.2–1.5.1, PDF pp. 35–49. The pinned repository supplied the baseline sources, the three facade modules, the verification script and module order, and the referenced phase-1 and phase-4 findings. One auditor; no delegation. No repository write was performed.

I found one **major verification-tooling defect**, in a pre-existing script used by the campaign, and one **minor packet-scope defect**. Independent checks reproduce the statement freeze, successful elaboration of all 22 modules, and all 13 reported axiom footprints. The tooling defect did not invalidate this independently checked elaboration. The remaining construction obligations and the limits of the proposed helper reuse are dispositioned individually below.

The following eight restatements were recorded from comment-stripped signatures and defining equations before reading their surrounding implementation prose. The subsequent comparison found no disagreement with their docstrings.

| File · promotion candidate | Blind restatement |
|---|---|
| `Halting.lean · halts_iff_eq_of_computes` | For any alphabet and fixed machine computing the total string function `g`, `(∃ t, M.ComputesInTime x w t) ↔ w = g x`. This characterizes completed outputs. It requires neither a finite alphabet nor a uniform time bound. |
| `Composition.lean · computesInTime_iff` | For a Boolean machine and specified input, output, and time, `M.ComputesInTime x w t` is equivalent to the initialized run being halted and having output exactly `w` at time `t`. No totality or minimal-halting-time claim is made. |
| `Encoding.lean · codeMapAction` | Any function between state types maps the action's optional successor state; input movement, work writes and movements, and emission are unchanged. `none` stays `none`. Injectivity is unnecessary. |
| `Encoding.lean · codeMapCfg` | Any function between state types maps the configuration's optional state and preserves every other field: input position, work tapes, work-head positions, and output. |
| `Encoding.lean · codeMapCfg_apply` | Applying a mapped action to a mapped configuration equals mapping the result of the original application. This holds even for a noninjective state function. |
| `Encoding.lean · codeRelabelTM` | A state equivalence maps the initial state forward. Each transition maps the current state backward, performs the original transition, then maps its optional successor forward. Alphabet and tape count are unchanged. |
| `Encoding.lean · codeRelabel_step` | From any mapped configuration, one relabeled-machine step equals the mapped original-machine step, including the halted case. |
| `Encoding.lean · codeRelabel_run` | For every input and natural time, the initialized relabeled run equals the mapped initialized original run at that same time. The stated theorem concerns initialized runs; it does not quantify over arbitrary starting configurations. |

For the first characterization, choose a completed computation of `g x` from `hM x`. A completed computation of `w` has the same output by `ComputesInTime.output_unique`; conversely, substituting `w = g x` gives the chosen computation. For the second characterization, unfold `ComputesInTime` and `ComputesInTimeAndSpace`. The existential space variable is constrained only to equal `M.tm.spaceUsed (M.tm.initCfg x) t`, so that very natural number supplies the reverse-direction witness. These are distinct useful facts: one characterizes the graph of a total function after existentially quantifying time; the other unfolds a fixed-time predicate without assuming totality.

The promotion recommendations are as follows.

| Candidate | Recommended public name and home | Statement requirements before promotion |
|---|---|---|
| A's completed-output characterization | `Turing.FinTM.Computes.exists_computesInTime_iff`, in `Finite.lean`. The requested `Computes.halts_iff_eq` is also acceptable if its docstring explicitly says “halts with completed output `w`.” | Keep its arbitrary-alphabet statement and `M.Computes g` hypothesis. No mathematical repair is needed. Do not replace completed output by an intermediate emitted prefix. |
| B's fixed-time characterization | `Turing.FinTM.computesInTime_iff`, in `Finite.lean`. | Generalize the unnecessary `Bool` restriction to `{Symbol : Type}` before sharing. No `Fintype` or `DecidableEq` assumption is needed. Keep this lemma as well as A's. |
| C's state mapping and relabeling | A non-vendored `TuringMachine/StateRenaming.lean`, depending on the raw deterministic model. Reuse the existing public name `Turing.Action.mapState`; add `Cfg.mapState`, its application lemma, `MultiTapeTM.relabelState`, and step/run correspondence. | Move the existing `Action.mapState` out of `Oracle.lean` into the shared lower layer and import it from Oracle and Encoding. Retain arbitrary functions for action/configuration mapping and an equivalence for machine relabeling. Name the current run lemma explicitly as an initialized-run lemma, such as `relabelState_runFrom_init`. An arbitrary-starting-configuration version would be a useful additional theorem, requiring its own checked statement. Preserve the generic universes and avoid new finiteness assumptions. |

An arbitrary state function is insufficient for relabeling a whole transition table: if it identifies two states with different emissions on the same scanned symbols, the target state would need two different transitions. No such issue affects action application, which receives its action explicitly. Oracle's embedding also adds a tape and query states; generic state renaming should factor out its state-mapping component, not replace the entire oracle embedding.

The independent freeze comparison covered **eight modified modules**, containing **45 pre-existing explicit declarations**, and identified **85 new private explicit declarations**:

| Module | Pre-existing declarations checked | New private declarations |
|---|---:|---:|
| `TuringMachine/Composition.lean` | 8 | 31 |
| `TuringMachine/Encoding.lean` | 18 | 18 |
| `TuringMachine/Universal.lean` | 3 | 0 |
| `Uncomputability/Computable.lean` | 2 | 0 |
| `Uncomputability/Diagonalization.lean` | 4 | 0 |
| `Uncomputability/Halting.lean` | 5 | 1 |
| `ClassP/Examples.lean` | 3 | 15 |
| `ClassP/TimeConstructible.lean` | 2 | 20 |

Every pre-existing comment-stripped declaration header agrees with its baseline header. Independently reproducing the textual diff gives exactly 15 removed lines: twelve `sorry` lines and the three specified docstring closing lines. All other changes are additions. All 19 attached Lean modules have the Git blob hashes in the audited commit. The commit comparison reports exactly the eight modules above and four intervening commits; the manifest and toolchain files are unchanged. The added source contains no new `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, option command, or attribute command. The added imports are precisely the listed Fintype modules.

All three docstring appendices accurately describe implementation choices. The counter appendix states the proved potential bound and final emission charges. The conditional appendix records the first-emission invariant, live administrative state, and absorbing-halting argument. The coding appendix correctly distinguishes the private action mapper from the older sketch's `Action.mapState` name and describes eliminating `hk` before relabeling. None changes the mathematical claim or attribution.

The delivered machines were checked against the audited transition schedules and the source model's write-before-move, clamped-input, and append-only-output semantics.

* `pairDiagTM` has six active states and no work tape. States 0 and 1 emit each input bit twice, with the first emission stationary and the second moving right. States 0 and 2 emit the two separator bits at the right blank. State 3 makes the unconditional first left move; state 4 scans left and then moves right from the left blank; state 5 copies once and halts. Thus, for input length `n`,

  $$
  2n+2+(1+n+1)+n+1=4n+5\le 6(n+1).
  $$

  For `n=0`, the five transitions emit `false`, emit `true`, move left, move right, and halt. The output is exactly `pairEncode [] [] = [false,true]`. This is the corrected phase-4 schedule, including its separate initial rewind transition.

* `palTM` implements the copy/rewind/test table from the phase-1 findings. The right-blank copy transition moves only the input head left; the left-blank rewind transition moves the input head right and work head left together. The work head is then at cell `n−1`. Matching comparisons move the two heads in opposite directions; a mismatch emits `false` and halts. A successful run costs

  $$
  (n+1)+(n+1)+(n+1)=3(n+1).
  $$

  At `n=0`, the work head reaches `−1`, and the three boundary transitions emit `[true]`. The test state's acceptance on an input blank is sound on initialized runs: the established scan invariant places the work head at `−1` after all comparisons. It need not validate arbitrary corrupted configurations. This matches the previously audited adaptation of AB Examples 1.1 and 1.4, rather than asserting the book's unpadded numerical bound in this model.

* `counterTM` exactly implements the four-state count/carry/rewind/emit table in the phase-1 reaudit. Counting advances the input once per increment. Carry clears the initial true bits, writes a final true bit, and rewind returns through the untouched blank at work cell `−1`. If `r = counterCarry (i.bits)`, one increment costs `r+1+r+1 = 2r+2` transitions. The proved local identity and bit bridge give

  $$
  \operatorname{popcount}(i+1)+r=\operatorname{popcount}(i)+1.
  $$

  Consequently, if elapsed time `t` satisfies the invariant at count `i`,

  $$
  \begin{aligned}
  (t+2r+2)+2\operatorname{popcount}(i+1)
    &=t+2\operatorname{popcount}(i)+4\\
    &\le 4i+4=4(i+1).
  \end{aligned}
  $$

  The base case has `t=0` and `popcount(0)=0`. At count `n`, nonnegativity of the potential yields `t≤4n`. Entering emission costs one step, emitting costs `length(n.bits)` steps, and the final blank halts in one step. Therefore

  $$
  \begin{aligned}
  t+1+\operatorname{length}(n.\mathrm{bits})+1
   &\le 4n+\operatorname{length}(n.\mathrm{bits})+2\\
   &\le 5n+2\\
   &\le 5(n+1).
  \end{aligned}
  $$

  Here `counter_bits_length` supplies `length(n.bits)≤n`, including zero. The empty input takes exactly two transitions and emits `[]`. Thus `c=5` is valid for every `n`.

  `counterInc_bits` is the correct canonical-representation bridge. Its cases are `[] ↦ [true]`; for `m>0`, `false :: m.bits ↦ true :: m.bits`; and `true :: m.bits ↦ false :: counterInc(m.bits) = false :: (m+1).bits`. These are respectively the representations of `0 ↦ 1`, `2m ↦ 2m+1`, and `2m+1 ↦ 2m+2`. Starting with `0.bits=[]`, exact equality to `(i+1).bits` preserves the absence of redundant high zeros. The potential lemma alone, which accepts arbitrary Boolean lists, would not establish that canonicality.

* `condTM` captures emissions with `reg.or a.output`, so the first emission wins and later nonemitting transitions preserve it. The invariant is `reg = simulatedOutput.head?`. Even when the simulated successor is `none`, the composite successor is `some (.inl (none, reg))`: the composite remains live. It starts rewinding only from that administrative state. For an input-head position `j`, the first left move gives `max(j−1,0)≤n`, after which the scan reaches 0 and the final right move reaches 1. This includes both boundaries and `n=0`.

  The controller's work tapes are separate from the fresh branch tapes, and its simulated emissions do not reach the real output. If the register is empty at dispatch, `reg.map ... = none` halts without output; that case is excluded by the theorem's singleton-output hypothesis. An early emission followed by divergence never dispatches. Under the hypothesis, the first completed controller computation identifies the register with `p x`. The expression `branchTM M₁ M₂ false` in the transition dispatcher does not force the false branch: the Boolean parameter affects only that machine's initial state; its transition function is independent of the parameter, and dispatch chooses the initial state using the register.

The remaining small gadgets also conform to their sketches. `constTM` emits the fixed word and uses one final halting step, including an empty word. `ifEqTM` tests the boundary after the last expected bit, so an extra input symbol is rejected, while an early blank or mismatching bit selects the other emission chain. The bound is at most `w₀.length + max u.length v.length + 2` before absorbing it into the stated linear budget. `pairDecode` consumes aligned pairs, recovers either doubled bit, and treats `[false,true]` as the separator; its round trip proves injectivity, including empty components.

There is no degenerate-state arithmetic defect in `exists_codeTM`. The initial state supplies an inhabitant, hence

$$
1\le\operatorname{card}(M.\mathrm{State}),\qquad
(\operatorname{card}(M.\mathrm{State})-1)+1=\operatorname{card}(M.\mathrm{State}).
$$

For a singleton state type the witness has `numStates=0`, and its actual state type is `Fin 1`, as required by `CodeTM`. An empty state type cannot support the supplied machine. Eliminating `hk` changes no alphabet or tape semantics. State relabeling preserves whole configurations apart from the state coordinate; the existential space witness is then recovered directly in both directions of the public theorem.

All nine remaining sorry declarations retain their audited forms. For the five in modified files, their complete docstring, declaration, and `sorry` body were compared byte-for-byte with the baseline. The other four reside in files untouched by the pinned commit comparison, whose attached contents match their repository blobs.

| Remaining declaration | Sketch disposition after epoch 1 |
|---|---|
| `computesFunInTime_comp` | The buffered two-phase construction remains implementable. Preserve output redirection, fresh second-phase tapes, and the monotonicity argument `length(f x)≤T₁(length x)` followed by `T₂(length(f x))≤T₂(T₁(length x))`. A bounded simulation invariant is still needed. |
| `exists_comp_partial` | Retain the compulsory first left move on the buffer, the right-boundary initial tag for an empty intermediate word, and clamping at both virtual boundaries. The two directions concern completed outputs and must exclude halting during administrative transitions. |
| `alphabet_reduction` | The fixed-width block construction, all-blank encoding of logical blank, and `k=0` case remain compatible with the model. No new helper invalidates the audited sketch. |
| `one_work_tape` | The marked-payload enlarged alphabet and sweep construction remain obligations; `k=0` is handled by an unused work tape. The new small-machine constructions do not discharge the sweep invariant. |
| `nonnegative_heads` | Preserve the detectable origin flag, independent folded payloads, stationary crossings at the fold, and safe behavior on nonembedded input symbols. The new counter's negative work-head visit is not a counterexample: this theorem constructs a different machine. |
| `oblivious_of_mem_DTIME` | Preserve the all-false-input simulation of the constructibility witness, fixed sweeps, parked real input head, and fixed final time. The newly proved identity example alone does not replace the arbitrary constructibility witness. |
| `exists_effectiveMachineCode` | The aligned parser is now an explicit list function, but its in-model implementation, record validation, short-circuit rejection, padding handling, and canonizer remain to be constructed. A Lean list parser alone is not an in-model parsing machine. |
| `universal` | Code-first preprocessing and the marked virtual left boundary remain essential. The total-function corollary is not a replacement for this partial evaluator construction. |
| `timed_universal` | Preserve buffered output, deadline-inclusive halting, timeout at `t=0`, and the bounded clock simulation. The ordinary counter is relevant infrastructure, not a completed timed evaluator. |

In particular, B's `leftCfg`/`rightCfg` suite is sound within its actual hypotheses but is not already a buffered-composition simulator. Both embeddings preserve the original input parameter, native input position, and output list; `leftAction`/`rightAction` pass emissions through. For example, a first component emitting a bit changes the embedded real output, whereas composition phase one must keep that output empty and write the bit to a buffer. A second component reading `y` cannot use the same-input configuration equation directly when the physical input is `x`. Moreover, `rewind_scan` and `rewind_from_any` inspect the native input and preserve work heads, so they do not rewind a buffer work head. Epoch 2 can reuse the tape-partition and induction patterns, but must add the buffer representation and virtual-input relation. The untimed existential conclusion of `rewind_from_any` also supplies no public numerical bound for the timed composition proof.

The placement of these helpers after the two remaining composition theorems is an additional practical constraint: Lean has no forward references. A fill that uses them in those earlier proof bodies must first move the required private infrastructure above its use, preserving its statements, or place genuinely shared infrastructure in an earlier imported module. This is a source-order/refactoring obligation, not a false helper statement. No new private name is directly referenced from another source module; public theorems intentionally depend on their own private helpers.

The assembly checks follow the actual quantifier scopes. `Computes.exists_computesFunInTime` and `UC_not_computable` use no evaluator. The former takes finite suprema of chosen halting times, with positive-length inputs vacuous over an empty alphabet. The latter normalizes the hypothetical total decider, relabels it, and chooses its fixed code using `decode_encode`; it never executes encoding or decoding.

`universal_quadratic` chooses one evaluator before quantifying over the simulated machine and uses only `(hCU x).1`. With `(T n+1)²≥1`, its absorption is exactly

$$
C_U\bigl(c_1(T(n)+1)^2+1\bigr)
\le C_U(c_1+1)(T(n)+1)^2.
$$

`UC_computable_of_HALT_computable` likewise chooses one evaluator before the per-input cases. It constructs the diagonal HALT decider, the self-pair/evaluator/postprocessor branch, and the constant-true branch using the stated gadgets and three applications of `exists_comp_partial`. A positive HALT answer supplies an actual decoded halting witness; `(hC α).1` supplies the evaluator's completed output. Output uniqueness identifies whether that output is `[true]`. A negative answer selects the constant branch. Neither proof uses the evaluator's converse clause or requires a globally named evaluator shared with other theorems.

The independent elaboration used Lean 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, and mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The locally available dependency checkouts used by the sweep matched the manifest and had clean tracked source trees. All 22 module sources came from the verified packet or the pinned repository. I used a fresh output tree, the prescribed dependency order and direct Lean invocations, checking each actual process exit code and newly generated `.olean`; no `lake build` was used. A narrowly scoped executable-path compatibility shim was needed in the auditor's runtime. Imported dependency caches were reused; they were not rebuilt from scratch.

Result: **22 successful process exits, 22 fresh module oleans, zero `error:` lines, exactly nine `declaration uses 'sorry'` warnings**. The only other warnings were the three pre-existing style/unused-variable warnings in `Configuration.lean`.

All 13 requested `#print axioms` results were reproduced. `pairEncode_injective` uses `[propext, Quot.sound]`. The other eight listed results without admissions use `[propext, Classical.choice, Quot.sound]`: the constant machine, comparator, conditional, diagonal pairing, coding relabeling, palindrome, identity constructibility, and finite-length time-bound bridge. The four remaining listed results have those usual axioms plus `sorryAx`. Traversing the checked environment's constant dependencies identifies their precise remaining admitted theorem dependencies:

| Theorem | Reachable declarations among the nine remaining sorries |
|---|---|
| `universal_quadratic` | `alphabet_reduction`, `one_work_tape`, `universal` |
| `UC_not_computable` | `alphabet_reduction`, `one_work_tape` |
| `UC_computable_of_HALT_computable` | `exists_comp_partial`, `universal` |
| `HALT_not_computable` | `alphabet_reduction`, `one_work_tape`, `exists_comp_partial`, `universal` |

Thus the dependency explanation is correct. The phrase “four assembly theorems” needs precise bookkeeping: of the four newly filled Batch A targets, the finite-length time-bound bridge is admission-free; the fourth admission-bearing item in the displayed footprint list is the already-proved consequence `HALT_not_computable`. None of these parametrized theorems currently depends on `exists_effectiveMachineCode`; constructing an inhabitant remains a separate obligation.

The independent sweep also exposed a defect in the prescribed verification script. At lines 31–36 of [`scripts/lean_check_tree.sh`](https://github.com/Shilun-Allan-Li/tcslib/blob/d3393b35764710ff3d7ae538d5133284291d9ef4/scripts/lean_check_tree.sh), the status of the command substitution running Lean is discarded; the script checks only for the text `error:` and then exits 0. In an isolated copy, I supplied a test executable named `lean` that printed `compiler terminated without diagnostics`, exited 23, and created no output. The unchanged checker returned 0 and created no `.olean`. This is a concrete false-success path, not evidence that the present Lean proofs failed. The documented sweep recipe's `|| break` also does not propagate a failing status as a failing overall shell command.

The fix is to capture and propagate Lean's status, reject a missing output, prevent stale output from satisfying that check, and make the sweep exit unsuccessfully on a failed module. The independently checked 22-module result above already used these stronger conditions. This issue is major for the reliability of the campaign's verification gate, while being pre-existing and separate from the mathematical content of the epoch-1 fills.

For delivery provenance, repository history corroborates the four integrated commits and their file ownership. The original delivery archives/git bundles and their asserted hash manifests are not included in the uploaded packet. Their mutual consistency, exact original bases, runner credential limitations, and cross-vendor independence therefore remain maintainer/agent attestations. Commit author metadata is not proof of those assertions. The source/hash/build checks here establish the delivered snapshot independently of those delivery-history claims.

The findings table follows. “Note” records a specific disposition or remaining obligation, not general approval.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `scripts/lean_check_tree.sh` · elaboration gate; attestation 2 | The pre-existing checker can report success after Lean fails. | The command's exit status is discarded. An isolated test executable exited 23 and produced no `.olean`; the unchanged checker returned 0. The sweep's `|| break` can also hide failure in the overall exit status. The independently guarded current sweep passed. | Propagate the compiler status; require fresh output; propagate a failed module out of the sweep. Keep exit/output evidence with future attestations. |
| 2 | minor | Audit brief · priority 1 and scope table | The packet miscounts the changed modules and omits one promised context document. | It says six modified modules but names eight; the independent diff confirms eight. `phase4-findings.md` is referenced as attached but is absent from the 30 file sections. It was obtained from the pinned repository for this audit. | Change six to eight and include the promised findings document in future upload-only packets. |
| 3 | note | Eight changed modules · freeze and soundness scan | The reported statement freeze is independently supported. | 45 old declaration headers unchanged; 85 new explicit declarations all private; all 19 attached Lean blobs match; exactly twelve sorry removals and three docstring-closing replacements; no added soundness bypass. | Retain this baseline and rerun the comparison after any promotion/refactoring. |
| 4 | note | `halts_iff_eq_of_computes`; `computesInTime_iff` | Both are sound promotion candidates with different roles. | Total-function completed-output uniqueness proves A; existentially choosing actual space proves B. B's Boolean restriction is unnecessary. | Promote both into `Finite.lean`, with the names and generalization specified above. Preserve totality only in A. |
| 5 | note | `Encoding.lean · codeMapAction` through `codeRelabel_run` | State renaming is sound; the machine construction correctly requires an equivalence. | Mapping application works for any function; identifying states with different transitions would invalidate unrestricted machine relabeling. The present run theorem is initialized-only. | Factor out a non-vendored state-renaming module, preserving `Action.mapState`; distinguish initialized and arbitrary-start run lemmas. |
| 6 | note | `Encoding.lean · pairDiagTM` | The delivered controller implements the corrected `4n+5` schedule. | Two emissions per first-pass bit, two separator transitions, `n+2` rewind transitions, second copy and halt; empty input takes five transitions. | No mathematical change required. Retain the explicit rewind charge. |
| 7 | note | `Examples.lean · palTM` | The delivered boundary transitions agree with the audited palindrome machine. | Copy and rewind align heads at input position 1 and work position `n−1`; complete matching runs take `3(n+1)` steps. Empty input accepts in three transitions. | No change required. Keep the reachable-configuration invariant when reusing the test state. |
| 8 | note | `TimeConstructible.lean · counterInc_potential`, `counterInc_bits`, `counter_count`, `timeConstructible_id` | The exact binary bridge and amortization justify `c=5`, including zero. | Each increment costs `2r+2`; elapsed time plus twice popcount increases by four. Emission adds `length(n.bits)+2≤n+2`; `n=0` takes two transitions. | No change required. Do not infer canonical output from the potential identity alone; retain the `Nat.bits` bridge. |
| 9 | note | `Composition.lean · condTM`, `exists_cond` | Register, administrative-state, rewind, and dispatch behavior match the audited design. | `Option.or` keeps the first emission; simulated halt remains a live composite state; fresh branch tapes and suppressed controller output are preserved; empty-register dispatch halts; early emission followed by divergence never dispatches. The apparent `false` parameter in the branch transition table does not select the branch. | No change required. Preserve the pre-halt hypothesis of `controlCfg_run` and the chosen first-halting-time argument. |
| 10 | note | `Encoding.lean · exists_codeTM`; three docstring appendices | Card arithmetic and the implementation notes are accurate. | `q₀` gives positive state cardinality, so subtraction/addition recovers the cardinality; one state gives `numStates=0` and `Fin 1`. All three appendices describe the delivered implementation without altering a claim. | No statement repair required. |
| 11 | note | Remaining nine sorries; B's proposed epoch-2 helper reuse | The audited statements/sketches are unchanged, but the helpers do not already implement buffered composition. | The existing embeddings preserve the same native input and pass output through; their rewinds leave work heads fixed. Buffering and virtual-input clamping need new invariants. Helpers also occur after the current composition proof bodies. | Preserve the nine statements. Move required helpers before use or into an earlier shared module; add buffer/virtual-input invariants and explicit time bounds. |
| 12 | note | Batch A; `HALT_not_computable` · evaluator scope and axiom footprints | The assemblies use exactly the intended interfaces; the remaining admissions are accurately located. | All 13 footprints reproduced; checked dependency traversal gives the four rows above. Only the quadratic corollary and HALT-to-UC reduction use an evaluator, each choosing one once and using only its forward clause. | Keep the dependency labels. Distinguish the clean finite-length bridge from the already-proved, admission-bearing HALT consequence. |
| 13 | note | Attestations 2 and 5 · verification and delivery provenance | Current elaboration is independently reproduced; original delivery history is only partially checkable. | 22 successful Lean exits and fresh oleans, nine expected sorry warnings, pinned dependencies. The original archives and their hash manifests are not supplied. | Preserve current build evidence; attach original manifests/archives if independent delivery-provenance verification is required. |

Notation glossary: `x` is an input word and `n` its length; `w` is a proposed completed output; `g` is the prescribed string function; `M`, `M₁`, `M₂`, `D`, and `U` are the machines named in the source statements; `e` is a state map or equivalence as indicated. `i` counts completed increments, `t` is elapsed time, and `r=counterCarry(i.bits)` counts the initial true bits cleared by the next increment. `popcount(i)=i.bits.count true`; `m` is the high-order integer in the binary cases. `j` is a native input-head position; `length` is list length; `card` is finite cardinality; `::` prepends a list element. `T` is the time-bound function, and `C_U,c₁` are its simulation constants from `universal_quadratic`. All other identifiers retain their Lean-source meanings.
