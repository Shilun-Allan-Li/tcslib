# Virtual-input layer: A-S1 fill-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 1 minor. No new duplication-debt finding. The fill gate may close.** The minor is a stale file-size figure in the pack; it does not affect the frozen surface or the proofs.

Audited: the sixteen-attachment `vhost-f1-bundle.md`, labelled commit `724108dd`, branch `complexity/arora-barak-ch3-4`; its patch identifies delivery commit `50f846477261689db83c4f4e629c9dad93a7ca96` and recorded base `44d25413044aed185a83ece08f7c29d0446d38ce`. Bundle SHA-256: `ea9dd29d12323f2b7f1b5088b2bb6dc871c3c1b0212b6e026bca91f66eb48d2c`.

This is a surface and proof-route audit. The supplied kernel-check premise is accepted; compiler execution, fresh-olean production, and axiom printing were not independently rerun. Source reconstruction and the checks described below were independently performed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1-1 | minor | Fill pack · repository-side attestations, file size | The current `VirtualInput.lean` has 508 lines, rather than the stated 506. | The delivery has 506 lines. The verified post-fill status-comment replacement adds two lines. Both the attached current source and the attached style log report 508. `Simulation.lean` remains 1,014. | Record a pack erratum distinguishing delivery: 506, audited post-refresh source: 508; preserve the shipped pack. |
| F1-2 | note — no findings | `Build/VirtualInput.lean` · `vhostSilent_layout` | The sole new private declaration states exactly the complete selected/capture partition. | Both equivalences hold for every index; the proof supplies the preimage for every value below `1 + m`, then identifies the sole remaining value with `vhostCap m`. At `m = 0`, selected tape zero and capture tape one exhaust the host. Restatement and derivation below. | None. |
| F1-3 | note — no findings | `Build/VirtualInput.lean` · seven forwarding contracts | The proofs follow the binding read/movement, lockstep, projection, interval, and emitting-halt routes. | The step cites `bufferTape_inputSymbol` and `virtualMove_correct`; the run chains valid arrival tags; both visited sets are equalities obtained pointwise at every time. The space sum has coefficient one at the same horizon and contains no output-length term. The emitting-halt result is derived from the step theorem. | None. |
| F1-4 | note — no findings | `Build/VirtualInput.lean` · two silent contracts | The silent flavor composes the two existing layers without another simulation induction. | Run correctness rewrites by `embedSilentTM_runFrom` and the forwarding run theorem. Space cites `embedSilentTM_visitedByTapeHead`, `embedSilentTM_spaceUsedByTape_cap`, and the forwarding space bound. The helper supplies disjointness and the surjectivity needed to account for every noncapture tape. | None. |
| F1-5 | note — no findings | `Simulation.lean` · two agreement transfers | The proof routes retain the strict-prefix guard, arbitrary common configuration, and unrestricted initial-state fields. | The step splits live/halted control and uses equality of the complete action. The run induction restricts the guard for its induction hypothesis and uses the guard at the last predecessor time. No guard at the final time or equality of `q₀` is added. | None. |
| F1-6 | note — no findings | Declared technique notes · control mapping and finite sums | Neither technique changes the frozen statements or import surface. | Mapping control to `Unit` is used only to consume input-only facts; input position and read reduce to those of the original configuration. The original transition still uses the original control. The two `sum_bij` proofs establish actual bijections onto the erased universes before applying `sum_erase_add`. | None. |
| F1-7 | note — no findings | Both owned files · freeze and header refresh | All existing declarations, signatures, imports, options, and nontarget bodies are preserved; the extra refresh is doc-only. | The patch has 203 added lines and eleven removed lines, each exactly `  sorry`, across only the two owned files. It adds just the one private helper. Reverse reconstruction matches both recorded preimage blob IDs. Delivery/current comparison isolates one replacement wholly inside the module comment. See the hash table below. | None. |
| F1-8 | note — no findings | Fill additions · failure mode 5 | The disclosed ledger, “new copies: none,” is supported for this fill. | No input-read, movement, embedding, or capture theorem is redeclared. The forwarding core adapts the sanctioned template to the new raw-machine transport and output prefix. The silent contracts cite the shared embedding facts. Existing buffered-host declarations are byte-unchanged; the patch does not touch the other predecessor files. | No new human debt acknowledgment required. Inherited 12.2c work remains outside this fill. |
| F1-9 | note — evidence scope | Attached replay, axiom, and lint logs | The supplied logs support the stated outcomes; they are not an independent execution by this auditor. | All five prescribed module exit records are zero, with no `error:` or sorry-warning lines. Eleven distinct axiom prints have the permitted footprints: the two agreement transfers use `[propext, Quot.sound]`, the other nine the standard triple. The attached Build lint log has zero FAIL. | Retain the distinction between inspected execution evidence and independently replayed execution. |

The sole new declaration was restated from its formal statement and proof: for any silent-host tape index, it is selected precisely when its value is below `1 + m`, and it is unselected precisely when it is the capture index. It asserts only layout arithmetic, with no machine, tag, positivity, or finiteness premise beyond its `Fin` types. Its two-way completeness agrees with the declaration prose and the binding statement-gate argument.

Explicitly, value preservation and the preimage `⟨j.val, hj⟩` give

\[
\begin{aligned}
j\in\operatorname{range}(\mathrm{Fin.castAddEmb}\ 1)
&\iff \exists i:\mathrm{Fin}(1+m),\ i.val=j.val\\
&\iff j.val<1+m.
\end{aligned}
\]

Since `j : Fin ((1 + m) + 1)`,

\[
\begin{aligned}
j\notin\operatorname{range}(\mathrm{Fin.castAddEmb}\ 1)
&\iff 1+m\le j.val<(1+m)+1\\
&\iff j.val=1+m\\
&\iff j=\mathrm{vhostCap}(m).
\end{aligned}
\]

Thus no ambient tape is omitted. For `m = 0`, these are exactly the partition `{0}` and `{1}`.

Each binding route was checked against the implemented body, rather than accepted from the agent's role table:

| Filled theorem | Observed route and fidelity |
|---|---|
| `MultiTapeTM.step_eq_of_agreeOn` | The halted branch uses `step_of_halt`. The live branch applies `h q (hq q hs)` to equate the complete transition actions. Exact match. |
| `MultiTapeTM.runFrom_eq_of_agreeOn` | Induction on the horizon, with the guard restricted for the induction hypothesis. At the successor, apply the step transfer at the predecessor time. Exact match; the final state may leave the agreement set. |
| `vhostEmitTM_step` | Halted control retains the supplied tag. Live control identifies buffer and bank reads, obtains the movement equation and new-tag validity from `virtualMove_correct`, and proves field equality for the transported action. The first inactive block of `bufferedSecondCfg_step` is removed; prefix associativity replaces its trivial output equality. A halting successor still receives the complete action. |
| `vhostEmitTM_runFrom` | Zero uses the original valid tag. Each successor consumes the prior arrival tag and the step theorem, then rewrites the iteration identities. No liveness or nonempty-word condition is introduced. |
| `vhostEmitTM_visitedByTapeHead_bank` | Unfold the visited image and prove its head function equal at every time using the run theorem. The existential arrival tag disappears under the bank projection. This proves equality, not containment. |
| `vhostEmitTM_visitedByTapeHead_buffer` | The same all-time argument projects exactly the integer input position minus one. The underlying range is `Finset.range (t + 1)`, including zero and the final time. |
| `vhostCfg_buffer_head_mem` | Project the run theorem, then use the source input position's `Fin` bound to obtain the inclusive interval `[-1, y.length]`. Both blank boundaries remain counted. |
| `vhostEmitTM_spaceUsed_le` | Bound the actual buffer visited image by that interval using `vhostCfg_buffer_head_mem`. This implements the binding projection/interval route directly, without needing an additional rewrite through the separately proved buffer-image equality. Identify each bank cardinality with its source counterpart, then sum by the complete buffer/bank partition. |
| `vhostEmitTM_emitting_halt` | Rewrite with the step theorem, substitute the live source state and halting/emitting action, and use append associativity. Neither the final bit nor simultaneous work actions are suppressed. |
| `vhostSilentTM_runFrom` | Obtain capture disjointness from `vhostSilent_layout`; combine the forwarding run with `embedSilentTM_runFrom`. There is no induction in this proof. |
| `vhostSilentTM_spaceUsed_le` | Cite selected-tape cardinality equality and the existing capture-growth bound. Rewrite the forwarding endpoint output, weaken growth to final capture-word length, and sum the selected contribution plus the sole capture tape. There is no new capture or simulation induction. |

For the universe technique, the inherited lemmas in `Simulation.lean` quantify `{S : Type}`, while the target's unchanged surrounding binder is `{S : Type*}`. The calls use `c.mapState (fun _ => ())`; their input-only expressions reduce as

\[
\begin{aligned}
(c.\mathrm{mapState}(\lambda\_\mapsto())).\mathrm{inputPos}
&\equiv c.\mathrm{inputPos},\\
(c.\mathrm{mapState}(\lambda\_\mapsto())).\mathrm{inputSymbol}
&\equiv c.\mathrm{inputSymbol}.
\end{aligned}
\]

The buffer-read fact is consumed by `exact`, and the movement fact needs no state-mapping transport lemma. These reductions are required by the supplied kernel-checked bodies. The constant function into `Unit` exists for an arbitrary state universe; no injectivity, state enumeration, or smallness assumption is used. The action remains `M.tr q c.inputSymbol c.workTapeSymbols` on the original source state. The mapping therefore restricts neither the machine nor the frozen target.

The emit sum uses the value-preserving bijection from `Fin m` onto all nonzero indices, `i ↦ vhostBank i`, whose value is `1 + i.val`. `Fin.addCases` supplies its surjectivity, including the empty bank when `m = 0`. The silent sum uses `Fin.castAddEmb 1` onto the complement of capture; its surjectivity explicitly consumes the helper's complement equivalence. Both sums end with `Finset.sum_erase_add`; neither can discard an extra tape. Imports are byte-unchanged. The claimed absence of `Fin.sum_univ_add` from the transitive import environment was not independently replayed; its absence is not needed to validate the chosen partition proof.

The space calculation is consequently

\[
\begin{aligned}
(vhostEmitTM\ M).spaceUsed(vhostCfg\ c\ b\ p\ pre,t)
&=M.spaceUsed(c,t)
  +(vhostEmitTM\ M).spaceUsedByTape(vhostCfg\ c\ b\ p\ pre,t,vhostBuffer\ m)\\
&\le M.spaceUsed(c,t)+\#\{-1,0,\ldots,y.length\}\\
&=M.spaceUsed(c,t)+(y.length+2).
\end{aligned}
\]

For capture, the cited bound gives, with natural-number subtraction,

\[
\begin{aligned}
(vhostSilentTM\ M).spaceUsedByTape(vhostSilentCfg\ c\ b\ p\ capPre\ out_0,t,vhostCap\ m)
&\le |(M.runFrom\ c\ t).output|-|c.output|+1\\
&\le |(M.runFrom\ c\ t).output|+1\\
&\le |capPre++(M.runFrom\ c\ t).output|+1.
\end{aligned}
\]

Adding the exact selected contribution gives the printed silent inequality, at the same `t` and with source coefficient one. The emitting inequality has no output term. The silent inequality conservatively charges the prior capture prefix; physical output `out₀` does not enter either ledger.

The boundary cases checked against the actual routes were:

| Case | Result |
|---|---|
| `m = 0`, `y = []` | Emit has only buffer; silent has buffer and capture. The source sum is empty and the buffer interval is `{-1,0}`. Neither sum proof assumes positive bank size or a nonempty word. |
| `t = 0` | The original tag witnesses the run theorem. Every existing work tape contributes its initial head singleton; both image equalities include that point. The silent capture contributes one visited cell regardless of its preloaded word length. |
| Initially halted source | Source and host remain fixed; the supplied valid tag can witness every time although halted control stores no tag. No induction requires a live source. |
| Empty word at either boundary | The movement lemma clamps the outward request and preserves the corresponding tag; inward movement crosses between the two adjacent boundaries. Its use through `Unit` changes neither position nor read. |
| Emitting halting transition with nonempty prefixes | The output equality is `(pre ++ c.output) ++ [bit] = pre ++ (c.output ++ [bit])`; the host then remains halted. Silent capture appends the same bit and preserves `out₀`. |
| Agreement set exited at the final step | The last predecessor is guarded; the final control is unrestricted. A further step would require an additional guard. For an empty agreement set, positive-horizon live starts fail the premise; halted starts remain valid. |

Freeze reconstruction used exact patch hunks, then independently checked declaration order, signatures, imports, and changed bodies. `VirtualInput.lean` has the same sixteen public declarations plus one new private theorem; `Simulation.lean` retains its forty-six declarations. The only changed existing bodies are the nine host targets and two agreement targets. Both current files contain zero comment-stripped `sorry` tokens.

To verify the status refresh beyond the supplied fill patch, I used the two locally available delivery source files as supplemental read-only evidence. Their Git blob hashes match the patch's postimage IDs. Reversing the patch on those bytes produces its preimage IDs; reapplying it reproduces the delivery bytes. Comparing delivery with the current attachment shows only the module status-comment replacement in `VirtualInput.lean`, and byte identity for `Simulation.lean`.

| File | Reconstructed base blob | Delivery blob | Current attached blob |
|---|---|---|---|
| `Build/VirtualInput.lean` | `e1eddb260b4b483251e187e07f431648f7366880` | `31a6e7c4d780c9dc444ab59eb69c460815a22f21` | `8279275ef9f1cc74633f7dd8ab037361fc76d69c` |
| `Simulation.lean` | `0d0233c91d5f6ce3fdb70db22ca5eee58ab8ef5c` | `873340ca3be1b091c97ab2bcaef5f5bbe170d46b` | `873340ca3be1b091c97ab2bcaef5f5bbe170d46b` |

The supplemental delivery-file SHA-256 values are `feaf4c044d86b191582731d91290878bde4a08f318cc8452ea5baa1f539feb55` for `VirtualInput.lean` and `38030b2f8ec61aed4d84610bd3b4c039aba0a48422e0f83d980bf6136dc09f23` for `Simulation.lean`. The source hashes and comparisons establish the file-level freeze; they do not independently authenticate commit ancestry, the original archive's complete checksum manifest, or the git bundle's prerequisite verification. No claim of reproducing those separate maintainer operations is made.

Notation glossary: source identifiers retain their Lean meanings. `m` is the source tape count; `i`, `j` are tape indices; `M` is the source machine; `c` its starting configuration; `t` the horizon; `b` the boundary tag; `p` the native input position; `y` the virtual input word; `pre`, `capPre`, `out₀`, and `bit` are the output prefix, capture prefix, fixed physical output, and emitted bit. `≡` denotes definitional equality, `#` cardinality, `|w|` list length, and `++` list concatenation. The displayed function applications use mathematical tuple notation for the corresponding curried Lean arguments.
