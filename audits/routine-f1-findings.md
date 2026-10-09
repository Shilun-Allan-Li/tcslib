**§12 epoch F1 — fill-gate surface audit**

**Verdict: PASS — 0 blockers, 0 majors, 1 minor, 4 notes.** The epoch meets the stated gate criterion. All 60 new private declarations have the required meaning in their uses; the 37 fills honor the inherited contracts. Public signatures and existing definitions are frozen, and all 19 F2 rows are byte-identical. The minor is a count in the campaign plan, not a Lean defect.

Audited on 2026-10-09. Reported repository snapshot: `bf1b6d04`, branch `complexity/arora-barak-ch3-4`. Independently verified input SHA-256:

```text
b610b75e630db240448226dd87ca960f0669a074e1a1efcd34e4e4cbf57833bb
```

The audit used the supplied patches, complete sources, inherited audit, reports, and maintainer logs. To check the exact two identities referenced by the pack, I also read the round-2 report’s “General seam derivation and state plumbing” passage in the earlier `routine-infra-r3-bundle.md`. References below are extracted source line numbers; the three source filenames mean files in `TCSlib/Complexity/TuringMachine/Build/`. No repository source was changed. This is a surface and contract-fidelity audit, not a fresh kernel replay.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1-1 | minor | `AroraBarakChapters3-4Plan.md:349` · F1B row | The row counts “four canonical statements” separately from the three space corollaries. There are three canonical statements. | The inventory is three general contracts, three canonical instances (`run`, `firstReturn`, `visitedByTapeHead`), two additive corollaries, one maximum corollary, and two release contracts: `3+3+2+1+2=11`. Four canonical statements would give twelve. The pack and agent B’s eleven-target inventory are correct. | Replace “four canonical statements” with “three canonical statements”. No Lean change. |
| F1-2 | note | `Embed.lean:329,789` · unused `hcap` | The stronger private identities do not compromise the advertised capture interpretation. | Both the action and configuration definitions prioritize selected-tape behavior. If `cap` is selected, both sides ignore capture and the transport equality still holds. The retained public premise excludes precisely that non-capturing case; the capture-space proof uses it. | Retain the frozen premise. No proof change required. |
| F1-3 | note | `Embed.lean:445,897` · Fill appendices | Both additions are truthful appendices; no earlier sketch text was replaced. | Removing each appended paragraph and restoring the closing `-/` reconstructs its original docstring byte-for-byte. The first describes interval containment; the second describes the independent host comparison actually used. | None. |
| F1-4 | note | `Catalog.lean:1638–1718` · seven `catalog_redirect*` helpers | The duplication is faithful, and the requested public head-trajectory lemma has the right scope and home. | All seven declarations, proofs, and docstrings match the attached `Wrappers.lean` originals after removing the `catalog_` prefix. Initialized head trajectories agree at every time, with no output or termination premise. | Queue the public projection in `Build/Wrappers.lean`, beside `redirect_run`; derive later visited-set and space results from it. No F1 gate dependency. |
| F1-5 | note | Patches, agent environment reports, and maintainer replay evidence | No integrated source depends on a delivered C shim. Historical replay and archive attestations have a narrower independent verification basis than the source checks. | Each patch changes exactly one Lean file. Imports/options are unchanged; no foreign-private reference, FFI hook, new axiom, unsafe declaration, or native-evaluation proof mechanism was added. Agents report using shims in their own environments; the maintainer separately attests exclusion from integration/replay. The attached logs contain the expected 37 axiom prints and 19 F2 warnings. Toolchain binaries, fresh `.olean` metadata, original ZIPs, checksum manifests, and Git bundles are not attached. | None for this surface gate. Keep agent setup, maintainer replay, and this source audit distinguished; do not describe the latter as an independently reproduced kernel/archive check. |

**The following restatements are derived from the declaration types and defining bodies.** They include the hypotheses and restrictions that matter; the agent role tables were checked against them. “Agrees” below means equality of complete configurations unless explicitly restricted to heads, visited sets, or cardinalities.

For `Embed.lean`, all fourteen additions agree with their claimed roles. In particular, the host-comparison helpers do not assume that their configurations actually arose from a source simulation.

| # | Private declaration · line | Body-derived restatement and role check |
|---|---|---|
| A1 | `embedSlot_selected` · 128 | For every source index `i`, searching the finite selection list at `ι i` returns `some i`. Injectivity identifies the unique preimage. |
| A2 | `embedSlot_unselected` · 142 | If host index `j` lies outside `Set.range ι`, its search result is `none`. Together with A1 this justifies selected/unselected tape cases. |
| A3 | `embedSilent_apply` · 258 | Applying the silent transported action to `embedSilentCfg c` equals transporting `a.apply c`, for every action and configuration, without `hcap`. Selected tapes take precedence; only an unselected capture tape records output. |
| A4 | `embedSilent_step` · 289 | One silent host step on a transported configuration equals the transport of one source step. This includes halted configurations and needs no capture-separation premise. The selected reads are exactly the source reads. |
| A5 | `embedEmit_apply` · 482 | Forwarded action application commutes with `embedEmitCfg`. The input move, selected writes/moves, successor, and output append agree; the unselected frame is unchanged. No liveness assumption. |
| A6 | `embedEmit_step` · 498 | One forwarding host step commutes with transport, for every source configuration, including a halted one and a live step whose successor halts. |
| A7 | `embedReturnAction` · 652 | Preserve all action effects and replace the successor by `some (Sum.inl q)` for source successor `some q`, or `some (Sum.inr ())` for successor `none`. Thus the transformed action always has a live successor. |
| A8 | `embedReturnCfg` · 657 | Preserve input position, work tapes, work heads, and output; encode a live state in the left summand and a halted state as the live right anchor. This is deliberately different from ordinary state mapping at a halt. |
| A9 | `embedReturnCfg_live` · 662 | If `c.state ≠ none`, the return encoding equals `c.mapState Sum.inl`. The hypothesis is essential: ordinary mapping does not revive a halted configuration. |
| A10 | `embedReturn_step` · 673 | If `R` executes return-encoded `N` actions on every left state and the right anchor idles, then `R.step (embedReturnCfg c) = embedReturnCfg (N.step c)` for every host configuration. No initialization, embedding, capture, or termination hypothesis. |
| A11 | `embedSilentRet_step` · 695 | For a live source configuration, the silent returning host’s step from the left-mapped transport equals the return encoding of the complete transported source successor. It also holds without `hcap`, with the interpretation in A3. |
| A12 | `embedThroughHalt` · 716 | For a state-preserving transport `E` satisfying the stated complete live-step equation, an initially live source that first halts at `T` gives: full left-mapped agreement at every `t<T`; the transported terminal data under the live right anchor at `T`; and exclusion of that anchor for every `t<T`. It assumes no terminal-result equation for `R`. |
| A13 | `embedEmitRet_step` · 815 | For a live source configuration, one forwarding returning step equals the return encoding of the transported complete successor, including the action’s output. |
| A14 | `embedReturn_visited` · 867 | Under A10’s two transition-table hypotheses, the returning host from `c.mapState Sum.inl` and closed host from `c` visit exactly the same cells on every tape at every finite horizon. This includes initially halted and nonterminating starts, without capture separation or a first-halt witness. |

For `Seam.lean`, all thirteen additions agree with their roles. The first-return core asserts exclusion only; it does not secretly assume or claim the second endpoint. Arrival is supplied by the separate endpoint theorem.

| # | Private declaration · line | Body-derived restatement and role check |
|---|---|---|
| B1 | `seamComp_step_left` · 128 | If `c.state ≠ some exit`, one composite step on `c.mapState Sum.inl` is the left mapping of `M₁.step c`. A halted `c` is allowed; the cut excludes dispatch, not halt. |
| B2 | `seamComp_step_right` · 144 | One composite step on any right-mapped configuration equals the right mapping of `M₂.step c`, including halt/absorption. No cut or endpoint premise. |
| B3 | `seam_stationary_apply` · 156 | Applying an action with zero movements, no writes, no output, and successor `some q` changes exactly the control field of any configuration to `some q`. This is action application, not a claim that a halted machine can step. |
| B4 | `seamComp_dispatch` · 162 | From any `c` with `c.state = some exit`, one composite step on its left mapping equals its constant-`entry` state mapping followed by right mapping. Every data field is preserved. |
| B5 | `seamComp_left` · 176 | If the source avoids `exit` at all times strictly below `T`, composite and left-mapped source configurations agree for every `t≤T`. No endpoint equation is required; the endpoint is included. |
| B6 | `seamComp_right` · 194 | If phase one reaches live `exit` configuration `c₁` at `T₁` without an earlier exit, the composite at `T₁+1+t` equals the right-mapped `M₂` run from `c₁` with its state changed to `entry`, for every natural `t`. |
| B7 | `seamComp_run_general` · 210 | With B6’s phase-one hypotheses and the phase-two endpoint equation at `T₂`, the composite reaches `c₃.mapState Sum.inr` at `T₁+1+T₂`. All configurations are arbitrary. |
| B8 | `seamComp_firstReturn_general` · 226 | With B6’s hypotheses and phase two avoiding `q₂` strictly before `T₂`, the composite avoids `Sum.inr q₂` strictly before the total time. No phase-two endpoint, liveness, or final-state premise. |
| B9 | `seamComp_visited_general` · 255 | With only the phase-one endpoint/live-exit/cut hypotheses, each composite visited set through `T₁+1+T₂` is contained in the union of the two actual phase footprints through `T₁` and `T₂`. No phase-two endpoint or termination premise. |
| B10 | `seam_ofWords_mapState` · 279 | Mapping a canonical seam’s state by any function produces the canonical seam at the mapped anchor with the same words and input. No injectivity requirement. |
| B11 | `seamRelease_fresh_step` · 600 | If `c.state = some anchor`, the release machine’s first step from the fresh-left state executes the anchor action and yields `(M.step c).mapState Sum.inr`. No setup step is charged. |
| B12 | `seamRelease_step_right` · 608 | Right-mapped release steps commute with source steps for every configuration, including halted configurations. |
| B13 | `seamRelease_run_pos` · 621 | From a source configuration at `anchor`, every strictly positive release time equals the right-mapped source run at the same time. A return or halt need not occur. Time zero is excluded because the adapter starts in the fresh-left state. |

For `Catalog.lean`, all thirty-three additions agree with their uses. `catalogCfg` fixes input position `1` and output `[]`; these are canonical-word routines, not assertions about arbitrary input/output frames. The raw configuration templates have total definitions at all indices. Their phase-invariant interpretation uses the index ranges and, for copy/transfer, the distinct-tape hypotheses of the trace lemmas.

| # | Private declaration · line | Body-derived restatement and role check |
|---|---|---|
| C1 | `catalogCfg` · 286 | Start with `Cfg.ofWords q w`, replacing only the work-head function by the supplied `heads`. State is `some q`, tape `j` is `bufferTape (w j)`, input position is `1`, and output is empty. |
| C2 | `catalogTrace` · 292 | At time `t≤L`, return `F t`; at `L<t≤2L+1`, return `R (2L+1-t)`; afterwards return `D`. Natural subtraction is used only in the indicated branch. |
| C3 | `catalog_trace_run` · 299 | The five local obligations—forward successors, the turn `F L→R L`, return predecessors, `R 0→D`, and `D→D`—imply that the entire run from `F 0` equals C2 at every time. The generic statement alone makes no first-exit claim. |
| C4 | `catalog_space_bound` · 334 | If a designated head lies between integer `−1` and natural `L` at every time, its visited cardinality at any horizon is at most `L+2`. The all-time premise is supplied by the concrete traces. |
| C5 | `catalog_space_one` · 346 | If the designated head is zero at every time, its visited cardinality at every horizon is `1`. The nonempty time image, including time zero, is essential. The hypothesis also implies the singleton described by the docstring. |
| C6 | `catalog_erase_take` · 356 | Under `r<w.length`, overwriting cell `r` of the stored prefix `w.take (r+1)` with blank gives exactly `bufferTape (w.take r)`. The statement concerns the whole tape. Its unused inequality is harmless; the equality even holds when the prefix has already ended. |
| C7 | `catalog_write_take` · 374 | For `r<w.length`, writing `w[r]` at cell `r` of `bufferTape (w.take r)` gives exactly `bufferTape (w.take (r+1))`. |
| C8 | `catalogClearF` · 383 | State `sweep`, original words, head `i` at integer `r`, other heads zero, with C1’s input/output fields. |
| C9 | `catalogClearR` · 388 | State `rewind`, word `i` replaced by its prefix of length at most `r`, head `i` at integer `r−1`, other words unchanged and other heads zero. At `r=0`, the word is empty and the head is `−1`. |
| C10 | `catalog_clear_trace` · 396 | From the canonical sweep seam, clear follows C2 with C8/C9, depth `(w i).length`, and terminal canonical `done` configuration with tape `i` empty, at every time. No condition on other words. |
| C11 | `catalogCopyF` · 451 | State `sweep`; overwrite the destination word by `(w src).take r`; place each selected physical head at `r`, others at zero. The source is intact when `src≠dst`; aliasing does not have that interpretation. |
| C12 | `catalogCopyR` · 457 | State `rewind`; overwrite the destination with the full source word; selected heads are at integer `r−1`, others at zero. |
| C13 | `catalogTransferR` · 463 | State `rewind`; first replace the source word by its length-`r` prefix, then the destination by the original source word; selected heads are at integer `r−1`. Distinct indices make these the intended separate updates. |
| C14 | `catalog_copy_forward` · 469 | For distinct source/destination and `r<(w src).length`, one copy step sends C11 at `r` to C11 at `r+1`. No blank-destination premise is needed for these already-constructed intermediate configurations. |
| C15 | `catalog_copy_trace` · 490 | For distinct indices and initially empty destination, the canonical copy run equals C2 with C11/C12, depth equal to source length, and terminal destination equal to the intact source. Equality holds at all times. |
| C16 | `catalog_transfer_trace` · 536 | Under the same two premises, transfer follows C11/C13 and ends with empty source and the original source word at the destination. All-time full-configuration equality, including the idle tail. |
| C17 | `catalog_compare_stop` · 596 | For every pair of words there is `d≤min(lengths)` with equal nonblank symbols at every earlier index, no equal nonblank pair at `d`, and equality of the two optional symbols at `d` iff the whole words are equal. This constructs the stopping certificate independently of the machine. |
| C18 | `catalogCompareF` · 626 | State `run`, unchanged words, and head `r` on each tape selected by `j=fst ∨ j=snd`. When the indices alias, there is one physical head and one selected action. |
| C19 | `catalogCompareR` · 631 | State `rewind v`, unchanged words, selected heads at integer `r−1`, other heads zero. The verdict is carried only in control. |
| C20 | `catalog_compare_trace` · 640 | Given C17’s stopping certificate for the actual two tape words, the comparison run equals C2 with depth `d`, C18/C19, and terminal verdict `decide (w fst = w snd)`, with every word unchanged. No distinctness premise. |
| C21 | `catalog_increment_split` · 733 | Every word is `replicate p true` followed by either nothing (`tail=none`) or a first `false` followed by the list in `tail=some v`. This supplies a genuine stopping decomposition. |
| C22 | `catalog_increment_value` · 747 | `incFixed` on that decomposed word is `tail.map (fun v => replicate p false ++ true :: v)`. Thus absent tail yields `none`, and present tail yields exactly the successor word. |
| C23 | `catalog_write_middle` · 759 | Replacing cell `pre.length` of `bufferTape (pre ++ a :: rest)` by `some b` yields exactly `bufferTape (pre ++ b :: rest)`, for arbitrary prefix, suffix, and bits. |
| C24 | `catalogIncF` · 779 | State `run`; word `i` is `replicate r false ++ replicate (p−r) true` followed by the original stopping suffix; head `i` is `r`. For the used range `r≤p`, this resets exactly the processed carry prefix. Other words and zero heads are retained. |
| C25 | `catalogIncR` · 787 | State `rewind tail.isSome`; word `i` is `replicate p false` followed by `true :: v` if the tail is present, otherwise no suffix; head `i` is integer `r−1`. This is the completed successor or wrapped word. |
| C26 | `catalog_increment_trace` · 797 | If the actual word has C21’s decomposition, the complete increment run follows C2 with depth `p`, C24/C25, and terminal `done tail.isSome` with the completed word. All times are covered; no success-only assumption. |
| C27 | `catalog_redirectState` · 1638 | A live source state becomes `some (inl (state, register))`. A halted source becomes `none` exactly when its optional last-bit register equals `some haltOn`; otherwise it becomes the live right loop. An empty register never matches. |
| C28 | `catalog_redirectAction` · 1645 | Copy input and work-tape effects, suppress physical output, and use C27 on the successor with register `a.output.or r`. A current emission replaces the old register before the halt decision. |
| C29 | `catalog_redirectCfg` · 1651 | Copy source input position, work tapes, and heads; set physical output to `[]`; encode source control using its actual `output.getLast?` as the register. |
| C30 | `catalog_redirect_loop` · 1658 | From any redirected configuration whose state is the live right loop, every run time returns that same entire configuration. No canonical-start assumption. |
| C31 | `catalog_redirect_apply` · 1670 | Applying C28 with the source output’s last bit to C29 of a source configuration equals C29 of the fully applied source action. The terminal emission is incorporated before successor encoding. |
| C32 | `catalog_redirect_step` · 1683 | One redirected step on C29 equals C29 of one source step, for arbitrary source configurations, including either post-halt register outcome. |
| C33 | `catalog_redirect_run` · 1712 | Every initialized redirected run equals C29 of the initialized source run at the same time. No restriction on output length, final bit, halting, or horizon. |

The conditional helper statements are not vacuous substitutes for the public contracts. A10/A14’s transition hypotheses are instantiated by definitional equality for both host pairs. B’s cores quantify over arbitrary configurations, and the canonical instantiations discharge their extra data by reflexivity. C3’s five local obligations are proved for every concrete trace. C17 and C21 construct the certificates used by C20 and C26; the latter do not assume the desired run conclusion. Copy/transfer require genuinely distinct tapes and a blank destination, exactly as their public contracts do; comparison deliberately permits aliasing.

**Contract fidelity is confirmed by the following derivations and dependencies.**

For A’s returning pair, `embedThroughHalt` implements the inherited five-step argument. Here `E`, `R`, `M`, `c`, and `T` are its own parameters.

1. The proof establishes positive time, without weakening the frozen hypotheses:

   \[
   T=0\ \Longrightarrow\ (M.\mathrm{runFrom}\ c\ T).\mathrm{state}
   =c.\mathrm{state}=\mathrm{none},
   \]

   contradicting `hc`. Conversely, `0<T` and `hlive 0` imply `hc`. The recorded equivalence therefore uses both first-halt hypotheses.

2. The component check is provided by A3–A6, A10, A11, and A13. Selected symbols agree by `embedSlot_selected`. Input movement and selected writes/moves agree; ordinary off-bank tapes do nothing. With `hcap`, a silent emission writes at the old capture length and advances once, using `bufferTape_append`; physical output remains `out₀`. Forwarding appends the emitted bit after `pre`. These effects occur before the successor is encoded, including a halting successor. The resulting step equation is exactly

   ```lean
   R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d))
   ```

   for live `d`. `some q` encodes to `some (Sum.inl q)` and `none` to `some (Sum.inr ())`.

3. Induction on `t<T`, using liveness at the predecessor and successor, gives

   ```lean
   R.runFrom ((E c).mapState Sum.inl) t
     = (E (M.runFrom c t)).mapState Sum.inl
   ```

4. Positivity gives `T−1<T` and `(T−1)+1=T`. Apply the same complete-step equation at `T−1`; `hhalt` then gives

   ```lean
   R.runFrom ((E c).mapState Sum.inl) T
     = { E (M.runFrom c T) with state := some (Sum.inr ()) }
   ```

5. At each earlier time the live source state maps into `Sum.inl`, which is disjoint from the right anchor. This supplies the entire third conjunct, not merely the terminal equation.

Both public returning-run proofs instantiate this core directly (`Embed.lean:809,856`). In contrast, both returning visited-set proofs instantiate A14 directly (`908,928`). A14 uses only A10’s host-step correspondence and ordinary iteration. An initially halted `c.mapState Sum.inl` remains halted on both sides; for a live start, A9 changes the initial return encoding to ordinary left mapping. Projecting every head position and taking the finite images proves equality. Neither through-halt contract occurs in this dependency path; no first halt or capture separation is imported.

For B, the two inherited full-configuration identities are realized literally, with the same domains:

```lean
-- seamComp_left: t ≤ T₁, with the strict phase-one exit cut
(seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t
  = (M₁.runFrom c₀ t).mapState Sum.inl

-- seamComp_right: every natural t, after the phase-one endpoint and dispatch
(seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + t)
  = (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr
```

B5 requires only the cut and is thus no weaker than the earlier report’s identity under all general hypotheses. B6 imposes no right-phase endpoint. The dispatch equation B4 preserves all non-control fields of arbitrary `c₁`; its live-state premise ensures that the constant mapping produces `some entry`, rather than trying to revive `none`.

The public canonical proofs (`Seam.lean:319–324,355–360,393–394`) are substitutions into the three general cores, using only `seam_ofWords_mapState`. The public general trio (`526,550,572`) uses those same cores. The cores precede the canonical proofs; there is no second canonical lockstep induction. Keeping the frozen public declaration order therefore does not violate “general first”.

For visited sets, an inclusive time `t≤T₁+1+T₂` has exactly the required placement:

\[
\begin{cases}
t\le T_1 &: \text{phase-one image witness at }t,\\
t>T_1 &: 0\le t-(T_1+1)\le T_2,
\quad\text{phase-two image witness at }t-(T_1+1).
\end{cases}
\]

This proves the advertised union containment without a phase-two endpoint. The same identities also imply equality with that union, but equality is not claimed as a new exported theorem. Cardinality monotonicity followed by union subadditivity gives the per-tape sum; summing gives total space. In the canonical maximum corollary, time zero places `0` in both phase footprints, so an idle `{0}` is contained in the other footprint. No sum-to-maximum shortcut is taken for arbitrary footprints.

The release proof executes the source anchor’s action once from the fresh state and uses B13 for every positive time. It excludes time zero by constructor disjointness. Its visited proof compares zero-time heads directly and all positive heads via B13, so it remains valid when the source halts or never returns. The unused endpoint hypotheses in the public exclusion statements do not conceal any weakening: those conclusions concern exclusion, while arrival is separately established or assumed.

For C, the generic trace gives the actual timeline

\[
\begin{aligned}
t=0,\ldots,L &: F(t),\\
t=L+1,\ldots,2L+1 &: R(2L+1-t),\\
t\ge2L+2 &: D.
\end{aligned}
\]

The concrete forward heads are `r`, return heads are integer `r−1`, and terminal heads are zero. Thus the forward segment visits every integer from `0` to the stopping depth, the return segment reaches `−1`, and every subsequent step is stationary. Distinct phase constructors exclude all exit anchors before the displayed time. The resulting ledger is:

| Routine / case | Forward + turn + return + entry | Chosen first-exit time | Frozen public budget | Complete touched interval and cardinality |
|---|---|---|---|---|
| Transfer | `L + 1 + L + 1` | `2L+2` | `3L+3` | `[-1,L]`, `L+2` on each selected tape |
| Copy | `L + 1 + L + 1` | `2L+2` | `3L+3` | `[-1,L]`, `L+2` on each selected tape |
| Clear | `L + 1 + L + 1` | `2L+2` | `2L+2` | `[-1,L]`, `L+2` |
| Compare | `d + 1 + d + 1` | `2d+2` | `2 min(lengths)+2` | `[-1,d]`, `d+2` on each selected physical tape |
| Increment, success | `p + 1 + p + 1` | `2p+2` | `2L+2` | `[-1,p]`, `p+2`; no visit to `p+1` |
| Increment, overflow | `L + 1 + L + 1` | `2L+2` | `2L+2` | `[-1,L]`, `L+2` |

The budget calculations are

\[
\begin{aligned}
(3L+3)-(2L+2)&=L+1\ge0,\\
d\le\min(|u|,|v|)&\Longrightarrow 2d+2\le2\min(|u|,|v|)+2,\\
p<L&\Longrightarrow p+1\le L\Longrightarrow2p+2\le2L\le2L+2,\\
|[-1,d]\cap\mathbb Z|&=d-(-1)+1=d+2.
\end{aligned}
\]

The analogous interval count applies to `L` and `p`. Exact intervals in the table describe the completed traversal; at shorter horizons only containment is asserted. All public space statements quantify over arbitrary horizons, which the stationary tail handles. Every untouched head stays zero and contributes exactly one cell, even at horizon zero. Comparison uses a disjunction to select tapes, so aliasing does not double a movement. C17’s common nonblank prefix also supplies every first-tape read on the rewind in both proper-prefix orientations. The unused `hd` in C20 is benign: its prefix premise already precludes a stopping depth beyond either word, and the bound is available when deriving the public budget.

W1 uses the inherited contract at **each** `u≤t` (`Catalog.lean:1265–1267`): its required liveness at `v<u` follows from `v<u≤t`. Consequently the head correspondence includes `u=t` when the source halts there; the final transition’s emission is not dropped. The source-bank head images are equal. For the capture head, output-prefix monotonicity gives

\[
|\mathrm{pre}|+|c_0.\mathrm{output}|
\le |\mathrm{pre}|+|(tm.\mathrm{runFrom}\ c_0\ u).\mathrm{output}|
\le |\mathrm{pre}|+|(tm.\mathrm{runFrom}\ c_0\ t).\mathrm{output}|.
\]

Containing the visited image in this integer interval gives cardinality at most

\[
|(tm.\mathrm{runFrom}\ c_0\ t).\mathrm{output}|-|c_0.\mathrm{output}|+1.
\]

Monotonicity also justifies the natural-number subtraction. No extra live-at-`t` assumption is used. W1 does not claim arbitrary behavior beyond the supplied horizon, when the host’s return state may execute a different routine.

W2 projects C33’s `.workTapePos` at every prefix, then takes image cardinalities (`Catalog.lean:1736–1742`). A halting source step performs its final write/move and updates the last-bit register before choosing halt versus live loop. Subsequently either outcome is stationary, just as the halted source is. Nonhalting sources are covered by the same all-time induction. No output or termination hypothesis was added.

The appropriate queued public lemma is the following initialized trajectory equality, universally quantified over `M`, `haltOn`, `x`, and `t`:

```lean
((redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t).workTapePos
  = (M.tm.runFrom (M.tm.initCfg x) t).workTapePos
```

It follows by projecting the existing private `redirect_run` in `Build/Wrappers.lean`. It is stronger than equality of visited cardinalities, uses no private name in its public statement, and is sufficient to eliminate the seven downstream copies. This is a proposed export shape, not a newly submitted Lean declaration.

**The adversarial instantiations below are direct evaluations of the supplied definitions, not claims of newly compiled Lean tests.**

| Instantiation | Result |
|---|---|
| Initially live source with `T=0` in either returning-run contract | `hhalt` forces the initial state to be `none`, contradicting `hc`. The old zero-time handover counterexample remains excluded. |
| Initially halted source in returning visited equality, any horizon | Ordinary left state mapping leaves `none`; both actual host runs remain halted. A14 treats this separately instead of incorrectly replacing the initial configuration by the live return encoding. |
| Identity tape selection with `cap` equal to a selected tape; source emits without writing | Selected-tape behavior wins and the emission is not recorded. The stronger private transport equation remains true because its right side also ignores capture. Public `hcap` excludes the purported capture use; the unguarded host-to-host visited equality remains valid. |
| One live source step writes `true` on selected cell `0`, moves that head right, emits `true`, and halts | At time `1`, the returning host has the written selected cell and head `1`. With silent prefix `[false]`, capture is `[false,true]` with head `2`; physical `out₀` is retained. Forwarding with prefix `[false]` has physical output `[false,true]`. Both controls are the live right anchor. A silent final action gives the same handover with no output-growth increment. |
| `T₁=T₂=0`, live exit configuration with an inactive head at `−4` and nonempty output | Exactly one dispatch changes control. That head remains `−4`, output is unchanged, and its visited set is `{−4}`. No canonical-origin or empty-output premise has entered the general theorem. With zero tapes the total space is zero. |
| Right phase halts on its first step; requested horizon extends past that halt | B2/B6 preserve the final action and then absorption. The general visited theorem still applies without a live right endpoint. |
| Source anchor writes a bit and moves right to a second state; second state moves left and returns to the anchor | Release control is fresh-left at time `0`, right-second-state at `1`, and right-anchor at `2`, with the bit retained and head restored. Both actions execute before a seam can dispatch on the released exit. A one-step source self-return likewise returns at time `1`, with no setup penalty. |
| Empty transfer/copy/clear word, and zero-width increment | The selected head positions are `0,−1,0`; first exit is time `2`, and the footprint is `{-1,0}`. Increment exits with overflow and the empty wrapped word. |
| Compare `[false]` with `[true]`; compare `[]` with `[true]` in either orientation | `d=0`, verdict false, first exit `2`, footprint `[-1,0]`. The rewind does not require a nonempty first word. |
| Compare `[true]` with itself, on distinct tapes or a single aliased tape | `d=1`, verdict true, first exit `4`, footprint `[-1,1]`. Aliasing selects one movement per physical tape. |
| Increment `[false]`; increment `[true,false]`; increment `[true,true]` | Respectively: `[true]` at time `2` with footprint `[-1,0]`; `[false,true]` at time `4` with footprint `[-1,1]`; overflow to `[false,false]` at time `6` with footprint `[-1,2]`. |
| W1 at horizon zero from a halted source; W1 at a terminal emitting step | The zero-time liveness premise is vacuous, source-bank footprints are initial singletons, and capture growth is zero with bound `1`. At a positive first halt, prefixwise use of `capture_run` includes the terminal emission and its extra head position. |
| W2 source emits `true`, later emits `false` on its halting transition | The final register is `some false`; `haltOn=false` halts and `haltOn=true` loops. Both retain the source’s work-head trajectory through and after halt. A source emitting nothing loops on halt for either `haltOn`; an infinite source still satisfies every finite-horizon correspondence. |

**Freeze and evidence checks were performed mechanically, independently of the reports’ assurances.** Each supplied patch was reverse-applied to its current source, its reconstructed old and current Git blob hashes were compared with the patch’s index line, and it was forward-applied again to reproduce the current source byte-for-byte.

| Check | Independent result |
|---|---|
| Patch ownership | A changes only `Embed.lean`; B only `Seam.lean`; C only `Catalog.lean`. |
| Inventory | Exactly 14/13/33 new private declarations: A has 2 definitions and 12 lemmas; B 13 lemmas; C 14 definitions and 19 lemmas. No new public declaration. |
| Original surface | Original declaration inventory/order, all 56 public theorem signatures, all original definition/inductive bodies, imports, options, namespace commands, and global variables unchanged. |
| Removed lines | Exactly 37 `sorry` body lines and A’s two docstring closing-line replacements. No other removed source line. |
| Documentation | Original declaration docstrings unchanged except the two append-only paragraphs verified in F1-3. Frozen skeleton-status labels are inherited wording, not an assertion that the newly filled theorems remain admitted. |
| Fills/admissions | A: 13 filled, zero remaining; B: 11 filled, zero remaining; C: 13 filled, exactly 19 remaining. Every remaining F2 theorem, including its original docstring and complete `by sorry` body, is byte-identical. |
| Redirection copies | Seven original wrapper declarations match exactly after consistent prefix removal, including proof text and documentation. |
| Supplied axiom log | Exactly 37 distinct theorem names, equal to the complete filled-target set. Every printed footprint is a subset of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. |
| Supplied sweep | Header records integration commit `2f67e910bb3a617d769524bb109bd9573cb1bbea`, all four requested module sections are present, and the completion marker is present. Zero `error:` lines. Exactly 19 sorry-warning locations, each matching one of the attached unchanged F2 declarations. The two A and five B unused-premise warnings agree with the source. |
| Supplied style log | `0 FAIL, 9 WARN over 39 files`; every WARN is a size warning. Current source lengths are 931/696/1851. The attached plan and design record the deferred Catalog split; it is not an undeclared size exception. |

| File | Reconstructed base Git blob | Current Git blob |
|---|---|---|
| `Embed.lean` | `75dc950744b262cfff8c00e62c65b3c020e92844` | `db10abdcdb3a33129cf0ef81a02329764ed1e7f7` |
| `Seam.lean` | `ef9ebc4bdcc8edfddb144b3cb666ba4855e7887a` | `8d88eac95776995f9cf263910737a09afbd83fcb` |
| `Catalog.lean` | `3b6303a6aafb496ab75219bb65a163fd1f98223d` | `b239b4089759c6ce10ff71bec7ba0682e7dfab42` |

For reproducible identification, the current source SHA-256 values are:

```text
cfce0d969cf1abf0187ab875b87d20d1104f737e0fc8b40c8504e2e54adbd47c  Embed.lean
5e8d93fe2031a79996b1be8b4df0c1b541d82120d11067012a681e3957bd3099  Seam.lean
9d896306befa195f88dc2900c62cda20090ae787b527872c49da49d5239e57aa  Catalog.lean
```

The fresh-`.olean` claim, the association with the reported repository commit graph, the delivery checksum counts `15/12/14`, and the Git bundles’ prerequisite `42d524b6` remain maintainer attestations. The packet does not include the binaries, archives, manifests, or bundles needed to reproduce those checks, and this environment has neither `lean` nor `lake`. The source reconstruction, freeze checks, sixty restatements, and contract-fidelity judgments above are independent of those missing artifacts. No shim was compiled or executed during this audit.

**Notation glossary.** No new machine notation is introduced. In the movement ledger, `L` is the relevant source-word length, `d` the first comparison mismatch or word-end position, and `p` the number of leading `true` bits (the first `false` position on success, or the full width on overflow). `F`, `R`, and `D` in the trace formula are `catalogTrace`’s forward configurations, return configurations, and terminal configuration. In the separate returning-proof derivation, `E` and `R` are the transport and returning-machine parameters of `embedThroughHalt`; all other names are source parameters. `|w|` denotes list length, and interval bars denote cardinality when applied to a finite set.
