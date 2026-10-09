# Virtual-input infrastructure: A-S1 statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 2 minors.** No new duplication-debt major. The eleven sorried contracts are mathematically true as written, subject to the inherited machine semantics and proved infrastructure. This is a statement audit, not a claim that their missing Lean proofs have been filled or independently kernel-checked.

Audited material: the supplied ten-attachment bundle, labelled commit `28a49d69`, branch `complexity/arora-barak-ch3-4`. Bundle SHA-256:

`b76a53aa8be41c5eb80700e2b5cdb91aa831f367ce213fe51ce6d2eb490bee64`

The source inventory is **8 new definitions, 11 sorried contracts, and 4 skeleton-time-proved lemmas**, not 7 + 11 + 4. All eight definitions were restated from comment-stripped bodies before their declaration docstrings were inspected. The four rider statements received the same treatment.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| A-S1-1 | minor | Audit pack · declaration inventory | The pack counts seven new definitions in total. | `VirtualInput.lean` contains seven `def` declarations: `vhostBuffer`, `vhostBank`, `vhostCfg`, `vhostEmitTM`, `vhostCap`, `vhostSilentTM`, and `vhostSilentCfg`. `Simulation.lean` adds `MultiTapeTM.AgreeOn`, giving eight. Every one was audited. | Record a pack erratum: eight definitions and 23 audited declarations overall. Preserve the shipped pack as required by `workflow.md`. |
| A-S1-2 | minor | `machine-library-design.md` §13, Z1 rider · promised `ofWords` form | The design promises selected-tape projections **and an `ofWords` transport form**; the delivered rider has only the four general projection lemmas. | `Embed.lean:943–973` exports exactly the four projections. They can be specialized to `c := Cfg.ofWords …`; there is no separately named new `ofWords` theorem. Thus the useful field facts are available, but the design's inventory is not synchronized with the delivered surface. | State explicitly that the promised form is supplied by specialization, or add the intended named specialization. If a whole-configuration identity was intended, state it separately with its frame, capture, head, and output parameters. |
| A-S1-3 | note — no findings | `VirtualInput.lean` · all seven definitions and nine contracts | Buffer hosting, both clamps, halting behavior, and output forwarding match the binding inherited behavior. | The head is the **integer** source input position minus one; the buffer receives an outer `none` write, so it is preserved; `virtualMove_correct` supplies the exact movement equation. The final source action is applied even when its successor state is `none`. See the statement checks and adversarial table below. | None required. |
| A-S1-4 | note — no findings | `vhostSilentTM`, `vhostSilentCfg` | The composite has no ambient tape accidentally reset by the default frame. | The embedding has image `{0,…,m}` inside `{0,…,m+1}`. Its complement is exactly `{m+1}`, the capture tape. The selected branch or capture branch handles every tape; the ambient defaults handle none. | None required. |
| A-S1-5 | note — no findings | `Simulation.lean` · `AgreeOn`, `step_eq_of_agreeOn`, `runFrom_eq_of_agreeOn` | The guarded transfer has the correct quantifiers for state-guarded agreement. | Agreement is uniform over reads on the chosen state set, while only live states at times strictly below the horizon must belong to it. A phase may leave the set or halt at the final step. This suffices for the Loop agreement layer and the state guards observed in the supplemental `clSlot_run` source; it is not a replacement for the separate tape/state transport. See customer-strength discussion and provenance limitation below. | None required for the state-agreement contract. A reachable-configuration transfer is a useful further generalization, not required by the observed read-uniform guards. |
| A-S1-6 | note — no findings | `Embed.lean` · four selected-tape rider lemmas | The riders expose only fields of the existing transports. | They identify tape contents and head positions at `ι i`, for arbitrary ambient frame parameters and prefixes. The selected branch takes priority even if `cap` is selected; these field identities therefore need no capture-disjointness hypothesis. Dynamic silent simulation still needs that hypothesis. | None required. The declared skeleton-time proof exception is benign. |
| A-S1-7 | note — no findings | Both space ledgers | Constants, horizons, and the coefficient of source space are correct. | The buffer interval has `y.length + 2` cells. Each bank visited set is equal to the source's at the **same** horizon. The silent wrapper adds only the capture contribution; its existing output-growth bound implies the stated final-word bound. | None required. The current silent bound is sufficient for the named query-decider application. |
| A-S1-8 | note — no findings | New surface · failure mode 5 | No new copied proof families appear in the submitted additions. | The new host is a public transformer using the existing `bufferTape`, `virtualMove`, `virtualNextTag`, and `embedSilentTM`. Its nine contracts are admissions, not copied proofs; the four rider proofs cite the existing selected-slot fact. Z5 adds a predicate and two contracts. The plan explicitly schedules the inherited deduplication for 12.2c. | No new debt acknowledgment required. This does not certify the contents or unchanged status of omitted predecessor files. |
| A-S1-9 | note — evidence limitation | Pack · elaboration, lint, change scope, and customer provenance | Source facts can be checked; all repository execution attestations cannot be independently replayed from this packet. | Independently counted source admissions: 9 in `VirtualInput`, 2 in `Simulation`, 0 in `Embed`; all eleven new admissions have a literal `Proof sketch`. The 1,005-line Simulation size and its justification are present. No build logs, pinned dependency environment, parent diff, Hardness inventory/source, or separate F2 findings file is attached. Limited supplemental customer source was inspected at a different commit, identified below. | Keep these distinctions in the resolutions. Supply pinned customer excerpts and the commit diff/logs if independently replayed provenance or execution verification is required; do not describe this audit as having performed that replay. |

## Blind definition restatements and daylight

The restatements below were recorded before reading the corresponding docstrings. “No daylight” means the body agrees with the declaration prose and the applicable §13 design, including §13a's canonical-layout refinement.

| Definition | Restatement from the body | Comparison |
|---|---|---|
| `MultiTapeTM.AgreeOn M N Q` (`Simulation:970`) | For every control state in `Q`, every input-symbol read, and every tuple of work-symbol reads, the two machines return the same complete action. Initial states and transitions outside `Q` are unrestricted. | No daylight. In particular, this is not merely equality on reads actually seen in one execution. |
| `vhostBuffer m` (`VirtualInput:106`) | Tape index zero of the `1 + m` work tapes. | No daylight. |
| `vhostBank i` (`VirtualInput:110`) | Tape index `1 + i.val`; every source tape gets a distinct nonbuffer slot. | No daylight. |
| `vhostCfg c b p pre` (`VirtualInput:120`) | Map live control `q` to `(q,b)` and preserve `none`; put the native head at `p`; install `bufferTape y` at tape zero with head `(c.inputPos.val : ℤ) - 1`; copy the source bank's contents and heads; set output to `pre ++ c.output`. | No daylight. The definition accepts invalid tags, but every relevant dynamic contract requires `VirtualTag`. A halted transport forgets the tag because its control is `none`. |
| `vhostEmitTM M` (`VirtualInput:138`) | Initial control is `(M.q₀,true)`. Ignore the native input read, read the virtual input from the buffer, and run the source transition on that read and the selected bank reads. Keep native input movement zero; never write the buffer; move its head by the clamped virtual move. Forward the bank operations and optional emission; attach the updated tag to a live successor, preserving a halting successor. | No daylight. All fields of a halting action survive except that there is no live control on which to store the tag. Initializing this machine does not itself load an arbitrary virtual word; the documented setup seam is essential. |
| `vhostCap m` (`VirtualInput:150`) | The last work tape, of value `1 + m`, in the silent host's `(1 + m) + 1` tapes. | No daylight. |
| `vhostSilentTM M` (`VirtualInput:158`) | Apply the existing silent capture embedding to `vhostEmitTM M`, selecting its entire bank by the value-preserving `Fin.castAddEmb 1` and using the added final tape for capture. | No daylight. This is genuinely a composition of existing transformers. |
| `vhostSilentCfg c b p capPre out₀` (`VirtualInput:167`) | Apply the same silent configuration embedding to `vhostCfg c b p []`. Preserve the virtual buffer and source bank, store `bufferTape (capPre ++ c.output)` on the final tape with its head at that word's length, and retain physical output `out₀`. | No daylight. The blank ambient tape and zero ambient head functions are unused, as proved next. |

For the silent layout, for every `j : Fin ((1 + m) + 1)`,

\[
\begin{aligned}
j\in\operatorname{range}(\mathrm{Fin.castAddEmb}\ 1)
&\iff j.val<1+m,\\
j\notin\operatorname{range}(\mathrm{Fin.castAddEmb}\ 1)
&\iff j.val=1+m\\
&\iff j=\mathrm{vhostCap}(m).
\end{aligned}
\]

The first equivalence follows because `castAddEmb` preserves values and its domain is `Fin (1+m)`. The second uses `j.val < (1+m)+1`; the third uses equality of `Fin` values. Thus capture is disjoint from the selected range and there is no third, ambient case. This includes `m = 0`: tape zero is the buffer and tape one is capture.

## The eleven sorried statements, literally

These are mathematical arguments for the statements, not replacement Lean proof scripts. They use the inherited `step` convention: a halted configuration is fixed; a live configuration applies the complete transition action, including writes and optional output, before taking the action's successor state.

1. **`step_eq_of_agreeOn` (`Simulation:981`).** If `c.state = none`, both steps equal `c`. Otherwise write `c.state = some q`; `hq` gives `q ∈ Q`, so `h` equates the two actions at `c.inputSymbol` and `c.workTapeSymbols`, and applying equal actions to the same configuration gives the stated equality.

2. **`runFrom_eq_of_agreeOn` (`Simulation:998`).** Induct on the number of steps up to the requested horizon, with equality at zero because both runs start at `c`. At time `u < t`, substitute the already-equal configurations and apply the preceding step lemma using `hq u`; if that configuration is halted, equality is automatic. No assumption about the control at time `t` is needed, and no equality of the two `q₀` fields is needed.

3. **`vhostEmitTM_step` (`VirtualInput:186`).** In the halted case take the original tag, because source and host configurations are both fixed. In the live case the buffer read is the source input read by `bufferTape_inputSymbol`, and the bank reads are identical by the transport's fields; choose `b' := virtualNextTag b (virtualMove b c.inputSymbol a.inputTape)`, where `a` is the source action. `virtualMove_correct` supplies both the exact buffer-head equation and validity of `b'`; all other configuration fields follow from the action definition and append associativity, including when `a.state = none`.

4. **`vhostEmitTM_runFrom` (`VirtualInput:201`).** At time zero, use witness `b` and the supplied tag hypothesis. For the successor step, apply the step contract to the transported source configuration and its valid arrival tag, then substitute the source and host iteration identities. This works after a halt as well as before it and introduces no nonemptiness or liveness premise.

5. **`vhostEmitTM_visitedByTapeHead_bank` (`VirtualInput:216`).** Apply the run contract separately at every `u ≤ t` and project `workTapePos (vhostBank i)`. The resulting head equals `(M.runFrom c u).workTapePos i`, independently of the existential arrival tag, so the two images of `Finset.range (t+1)` are equal. Thus the statement is equality, not merely containment.

6. **`vhostEmitTM_visitedByTapeHead_buffer` (`VirtualInput:230`).** The corresponding buffer-head projection at each time `u ≤ t` is exactly `((M.runFrom c u).inputPos.val : ℤ) - 1`. Substitution into the defining finite image gives exactly the stated right-hand side, with both time zero and time `t` included.

7. **`vhostCfg_buffer_head_mem` (`VirtualInput:246`).** The run identity gives the head as the integer source input position minus one. Since that position belongs to `Fin (y.length+2)`, its value lies between zero and `y.length+1`, so the transported head lies between `-1` and `y.length`, inclusively.

8. **`vhostEmitTM_spaceUsed_le` (`VirtualInput:262`).** Split the sum of work-tape visited-set cardinalities into tape zero and the bank indexed by `Fin m`. The bank equalities give exactly `M.spaceUsed c t`, while the buffer equality and interval lemma bound its cardinality by `y.length+2`. This yields the printed coefficient one, at the same horizon, without any output-length term.

9. **`vhostEmitTM_emitting_halt` (`VirtualInput:279`).** The hypotheses say that the action applied from the live source configuration has successor `none` and emission `some bit`. The host applies that same emission while mapping the successor to `none`, so its new output is `(pre ++ c.output) ++ [bit]`. Transporting the source step gives `pre ++ (c.output ++ [bit])`; append associativity makes these equal to the displayed contract, so the final bit is neither dropped nor duplicated.

10. **`vhostSilentTM_runFrom` (`VirtualInput:299`).** Apply `embedSilentTM_runFrom` with source `vhostEmitTM M`, the specified embedding, capture tape, and transported starting configuration; the required capture-disjointness follows from the layout arithmetic above. Substitute `vhostEmitTM_runFrom` and its valid arrival tag. The result is precisely `vhostSilentCfg` of the source endpoint, with capture prefix `capPre` and physical output `out₀` unchanged; no third simulation induction is needed.

11. **`vhostSilentTM_spaceUsed_le` (`VirtualInput:315`).** Split the silent host into the selected forwarding host and its sole capture tape. `embedSilentTM_visitedByTapeHead` gives the selected contribution exactly, and `embedSilentTM_spaceUsedByTape_cap` bounds capture by source output growth plus one. That quantity is at most the final capture-word length plus one, so the forwarding bound gives exactly the stated inequality.

The movement equation used in item 3 is literally the inherited one:

\[
(c.inputPos.val:\mathbb Z)-1
+(\mathrm{virtualMove}\ b\ c.inputSymbol\ a.inputTape:\mathbb Z)
=((\mathrm{moveInputPos}\ c.inputPos\ a.inputTape).val:\mathbb Z)-1.
\]

The existing `bufferedSecondCfg_step`/`_run` have the same arbitrary-source-configuration, valid-tag, arbitrary-native-position, existential-arrival-tag, and all-horizon shape. Z1 removes the inactive first block, generalizes to a raw machine, and permits an arbitrary output prefix. It does not weaken their treatment of empty input or halted configurations. Removing the inactive block is the declared canonical-layout choice; R1 supplies relocation/frame extension separately.

## Space calculation and the named consumer

The buffer bound counts **both** blank boundaries:

\[
\#\{-1,0,\ldots,y.length\}=y.length+2.
\]

Consequently,

\[
\begin{aligned}
\mathrm{space}_{\rm emit}(t)
&=M.spaceUsed(c,t)+\#\mathrm{bufferVisits}(t)\\
&\le M.spaceUsed(c,t)+y.length+2.
\end{aligned}
\]

The existing capture theorem is stronger than the newly stated capture allowance. Append-only output gives

\[
\begin{aligned}
\mathrm{space}_{\rm cap}(t)
&\le |(M.runFrom\ c\ t).output|-|c.output|+1\\
&\le |(M.runFrom\ c\ t).output|+1\\
&\le |capPre++(M.runFrom\ c\ t).output|+1.
\end{aligned}
\]

The subtraction is natural-number subtraction, and output monotonicity ensures it is the actual nonnegative growth. Adding the emit bound gives the silent statement. Existing capture-prefix cells need not all be visited during this run; charging their full length is conservative, not an undercount. There are no extra ambient tapes contributing unaccounted initial cells.

For the intended query-decider use in `NP^EXPCOM ⊆ EXP`, take an empty capture prefix and a source run whose complete output is a singleton answer. Every prefix output then has length at most one, so the silent bound is at most

\[
M.spaceUsed(c,t)+y.length+4.
\]

This preserves the source-space coefficient and suffices for that use. Loading/resetting the query buffer and capture tape, and joining repeated query segments, remain consumer obligations; no contract here falsely charges those operations to the lockstep window. This audit verifies the ledger's usable shape, not the separate oracle-class theorem.

## Adversarial instantiations

| Test | Substitution and result |
|---|---|
| Empty virtual input, left boundary | `y=[]`, source position zero, tag `false`, buffer head `-1`. A left request is clamped to zero movement; a right request moves to buffer position zero and sets the tag to `true`. |
| Empty virtual input, right boundary | `y=[]`, source position one, tag necessarily `true`, buffer head zero. A right request is clamped; a left request moves to `-1` and sets the tag to `false`. There is no missing nonempty-word premise. |
| Each boundary under the wrong tag | At the left boundary with tag `true`, a left request escapes to `-2`; at the right boundary with tag `false`, a right request escapes to `y.length+1`. Both are excluded by `hb`. This verifies that the tag hypothesis is necessary rather than redundant. |
| Stationary moves and repeated outward attempts | On a valid boundary tag, clamping produces zero movement, and `virtualNextTag b 0 = b`. Repeated attempts remain clamped. An interior stationary move also preserves either permitted interior tag. |
| Interior tags | For a one-bit word at source position one, both tags satisfy `VirtualTag`. Moving left reaches position zero with tag `false`; moving right reaches position two with tag `true`. Neither interior tag causes spurious clamping because the scanned bit is nonblank. |
| Zero source tapes | `m=0` leaves one emit-host tape, the buffer; the bank equalities have no instances. Silent hosting has exactly buffer and capture, with no hidden ambient tape. Source space is zero. |
| Zero horizon | At `t=0`, choose the original tag. Each existing work tape contributes its initial head singleton; the buffer image also has one element, and capture contributes one visited cell irrespective of the length already stored. Both inequalities hold. |
| Initially halted source | `c.state=none` makes both hosts initially halted. Every subsequent configuration, output, buffer head, bank head, and capture head is fixed. The existential tag can remain the supplied valid tag even though it is not stored in halted control. |
| Emitting halting action | Let `pre=[true,false]`, `c.output=[false]`, and `bit=true`. The host halts with output `[true,false,false,true]`; simultaneous source work writes and head moves are also executed. Every later step fixes this result. |
| Empty native input | `x=[]` gives `p : Fin 2`. Both possible native positions stay fixed because every live host action requests native movement zero, and halted configurations are fixed. Virtual-input behavior is independent of the native read. |
| Nonempty capture prefix and physical output | With `capPre=[false,true]`, `c.output=[false]`, and a new `true` emission, capture becomes `[false,true,false,true]` and its head moves from three to four. The arbitrary physical output `out₀` remains unchanged. |
| Agreement on the empty set | With `Q=∅`, agreement itself is vacuous. For a live start, the visit premise is possible at `t=0` but impossible at any positive horizon because of time zero; for a halted start, every horizon works and both runs are fixed. No false transfer is obtained. |
| Agreement on all states | With `Q=Set.univ`, read-uniform action equality gives equality of runs from any **common configuration**, even when `M.q₀ ≠ N.q₀`. It does not assert equality of their separately initialized configurations. |
| Halting before the horizon | If the common run halts at time `h<t`, the visit condition constrains only its live prefix; all later antecedents asserting a live state are false. The remaining steps are identities for both machines. |
| Disagreement immediately outside the set | Take two states, with `Q` containing only the first. Both machines move from the first to the second silently; at the second one emits `false` and the other emits `true`. Transfer is valid at horizon one, whose final state is outside `Q`; it cannot be applied at horizon two. Strict `< t` is the correct endpoint convention. |
| Read-dependent agreement only on the actual run | Two machines can agree forever on a stationary blank-tape run from one state yet disagree at that same state when the scanned cell is `some true`. This would require a weaker, per-configuration transfer hypothesis; `AgreeOn` deliberately does not cover it. The observed `clSlot_run` guards require agreement for **all** reads, so this is not their obstruction. |

Independent executable checks, using a small mathematical model rather than Lean, passed: 270 valid tag/movement cases for word lengths 0–8; 18 invalid-tag outward counterexamples; 33 tape layouts for `m=0,…,32`; 675 prefix/output/emission append cases; and 9,720 head/output trajectories covering word lengths 0–4, bank sizes 0–2, all period-three movement patterns, initial/early halts, and nonempty prefixes. These finite checks corroborate the arguments; they are not substitutes for the quantified proofs.

## Z5 customer strength

For Loop, choose `Q` to exclude the body-state constructor. The attached inventory says the forwarding table delegates every other state to the capturing table, exactly the all-reads equality required by `AgreeOn`. A non-body segment transfers as soon as its strict-prefix control invariant is supplied. Entry into a body state at the segment's final time is allowed; later execution of that body is not transferred. One-step phase identities use `step_eq_of_agreeOn`; the initial-configuration identity separately uses the two hosts' equal initial-state fields. Thus “collapse fourteen lemmas” includes simple field/projection reductions and shared prefix invariants, not fourteen applications of one endpoint equation without further premises.

The `clSlot_run` signature inspected in supplemental source has

```lean
(good : S → Prop)
(hagree : ∀ q, good q → ∀ inp work,
  host.tr (emb q) inp work =
    clSlotAction select emb (src.tr q inp (fun i => work (index i))))
(hguard : ∀ j < t, ∀ q,
  (src.runFrom c j).state = some q → good q)
```

Its guard is on the control state, and its equality is uniform over `inp` and `work`. The thirteen observed uses have state predicates such as `q ≠ exit`, a component unequal to `none`, exclusion of final constructors, or `True`. They do not introduce a tape-content or head-position guard. Therefore a per-configuration **agreement** hypothesis is unnecessary for those guards.

There is a separate typing issue: `clSlot_run` transports between different tape counts and state types, whereas Z5 equates runs on one carrier. Z5 must be applied **after** tape relocation and state transport produce the reference machine on the host carrier; the compared machines then use the same starting host configuration. It does not, by itself, replace the entire generic `clSlot_run` theorem or establish that transport. For the concrete injective constructor/pair state embeddings, one can extend the renamed source table to the host state type, use the existing unguarded state/block transport and R1 relocation to identify its run, then use Z5 on the image of the good source states. This is the appropriate composition of responsibilities; claiming that `runFrom_eq_of_agreeOn` directly accepts arbitrary `src`, `host`, and `emb` would be incorrect.

The fully generic `clSlot_run` also permits a noninjective `emb`; its complete heterogeneous statement is not a literal specialization of the new API. If preserving that entire private helper's generality becomes a retrofit requirement, a public guarded configuration-transport theorem would be the appropriate additional export. I do not interpret the current design's explicitly same-carrier Z5 contract as promising that stronger transport theorem.

**Evidence boundary:** the packet contains the Loop inventory but not Loop or Hardness source at `28a49d69`, nor the other two retrofit inventories. For the limited customer check, I inspected read-only source snapshots at commit `5588628cbbddea9546f616907364b608e15557fd`, without consulting development history or prior audit findings. The observed Loop constructor and fourteen-family descriptions match the attached inventory; the Hardness snapshot has thirteen `clSlot_run` call sites. This corroborates the customer shape but does not independently establish that those omitted files are unchanged at the audited commit.

Supplemental file SHA-256 values:

- `Build/Loop.lean`: `51842d285e66ff5da13b434f4652b333f43690086416f681165f4ff2267acb78`.
- `CookLevin/Hardness.lean`: `b1332ebc638a2ecd1c438d3f1a1e34a3669e0ae7afad32493d9949cdf2ffc6bb`.

## Rider restatements and declared anomalies

| Rider | Blind restatement |
|---|---|
| `embedSilentCfg_selected_tape` | At host tape `ι i`, the silent transport's entire tape function equals `c.workTapes i`. |
| `embedSilentCfg_selected_pos` | At host tape `ι i`, the silent transport's head equals `c.workTapePos i`. |
| `embedEmitCfg_selected_tape` | At host tape `ι i`, the forwarding transport's entire tape function equals `c.workTapes i`. |
| `embedEmitCfg_selected_pos` | At host tape `ι i`, the forwarding transport's head equals `c.workTapePos i`. |

All parameters in these statements are arbitrary as printed. They expose exactly the selected fields requested by D-R1; they make no claim about a run, time, space, capture disjointness, or canonical input configuration. They are thin public consequences of the existing private selection equation, not new machine-construction proofs. The skeleton-time exception is therefore benign.

The silent definition-by-composition is fully determined, with the required tape disjointness discharged arithmetically. The Simulation size deviation is real—1,005 lines—and its decision-13.5/D7 justification is explicitly recorded in the plan. No new contract consumes a machine's `q₀`: they all concern supplied configurations and `runFrom`; the `true` initial tag is valid at source position one even when the virtual word is empty. There is no hidden initial-configuration correctness assertion.

The new file cites the existing virtual-movement and buffering primitives rather than declaring replacements for them. The public `bufferedCompTM` remains a distinct sequential-composition customer, so retaining it is not new duplication. The plan's 12.2c decision explicitly schedules the inherited private-copy cleanup after the retrofit batches. The attachment set is insufficient to independently count every inherited copy or verify that every omitted predecessor was untouched; no such stronger provenance claim is made here.

## Recommended machine-checkable sanity exports

These are additions to weigh, not blockers for the present statements.

1. **Initial-tag validity and independence from `q₀`.** Export `VirtualTag (1 : Fin (y.length+2)) true`. Separately, prove that replacing a machine's `q₀` while keeping its transition table fixed does not change `runFrom c t`; instantiate this for the host. This is an `initCfg`-free way to express precisely what the current contracts do and do not consume.
2. **Transport injectivity for fixed parameters.** For fixed `b`, `p`, and `pre`, `fun c => vhostCfg c b p pre` is injective: project the bank, cancel the fixed output prefix, recover input position from the buffer head, and recover the optional source state by its first component. Do **not** assert joint injectivity in `(c,b)`: distinct tags give the same transported configuration when `c.state=none`.
3. **Native-head constancy.** For every host configuration `d`, not just a valid transported one, prove `((vhostEmitTM M).runFrom d t).inputPos = d.inputPos`; the transition always requests movement zero. Its finite trajectory image is the singleton `{d.inputPos}`. `visitedByTapeHead` indexes work tapes only, so a native-input version should use this input-position image rather than an invented work-tape index.
4. **Boundary and seam specializations.** Give named empty-word left/right clamp corollaries, and a silent emitting-halt projection showing the capture append and unchanged `out₀`. The general contracts already imply them; named forms would make the inherited regressions easy to preserve during 12.2c.

## Verification scope

Independently checked: attachment count and bundle hash; blind declaration inventory; all eleven literal contract shapes and sketches; four rider statements; layout arithmetic; boundary/halt/prefix cases; exact visited-set and space calculations; observed customer guard quantifiers; and the absence of newly copied proof families in the supplied additions.

Not independently replayed: Lean elaboration, axiom printing, fresh-olean creation, repository style scripts, the parent-to-`28a49d69` diff, or customer source identity at that commit. Source admission counts are not reported as independently reproduced compiler-warning counts. The separate F2 findings are absent, so the binding forwarding clauses were checked against the quoted A2 report, the pack, the design, and the supplied proved buffered-host template.

## Notation glossary

`M`, `N` are machines; `c`, `d` are configurations; `q` is a live control state; `Q` is the agreement set; `t`, `u`, `h` are nonnegative times. `m` is the source work-tape count; `i`, `j` are tape indices where used as such. `x`, `y` are native and virtual input words; `b`, `b'` are boundary tags; `p` is the native input-head position; `a` is the source action. `pre`, `capPre`, `out₀`, and `bit` retain their Lean meanings: physical-output prefix, capture prefix, fixed physical output, and emitted bit. `S`, `H` are source and host state types; `src`, `host`, `good`, `emb`, `index`, and `select` retain the names and roles in the displayed `clSlot_run` signature. `++` is list concatenation, `|w|` is list length, and `#A` is finite-set cardinality. `space_emit`, `space_cap`, and `bufferVisits` abbreviate the emitting host's work space, the silent host's capture-tape space, and the buffer's visited set, respectively, always from the transported starting configuration at the displayed horizon. All other code identifiers have their source meanings.
