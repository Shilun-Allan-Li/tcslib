# Epoch-2 independent adversarial audit

Audit target: [commit ee32391c](https://github.com/Shilun-Allan-Li/tcslib/tree/ee32391c), branch `complexity/arora-barak-ch1`, repository `Shilun-Allan-Li/tcslib`. Input: `epoch2-bundle.md`, SHA-256 `f5491c023bb2ad29b7dc96909ec69f456b32fbd8032ac188e086e84b63284d58`.

## Blind restatements of the 26 new public declarations

These restatements were recorded from comment-stripped declaration headers and definition bodies before reading their individual docstrings. The commissioning brief and the beginning of batch A's report had already exposed the intended construction; this is a docstring-blind pass, not a claim of complete prior ignorance. Proof tactics are outside this audit's scope. Line references below are to the extracted Lean files, not the concatenated bundle.

All names in this table are in `Turing.FinTM`, in `Simulation.lean`. Natural input positions range from `0` through `word.length + 1`; the two endpoints read blank. A work-tape `none` denotes blank, whereas an action's outer `none` denotes no write.

| # | Declaration · line | Independent restatement |
|---|---|---|
| 1 | `tapeBlocks` · 421 | Concatenates a `k`-indexed block, one distinguished value, and an `l`-indexed block, giving a function on `Fin (k + (1 + l))`. The element type is arbitrary. |
| 2 | `tapeBlocks_left` · 426 | At the inclusion of a left index `i`, this concatenation returns the original left value `a i`. |
| 3 | `tapeBlocks_buffer` · 431 | At the inclusion of any index of `Fin 1`, it returns the distinguished value `b`. |
| 4 | `tapeBlocks_right` · 437 | At the inclusion of a right index `i`, it returns the original right value `c i`. |
| 5 | `bufferTape` · 442 | Stores the Boolean word at integer cells `0,…,length−1`, and blank at every other integer. In particular, `some false` is a symbol, not blank. |
| 6 | `bufferTape_nil` · 446 | The empty word produces the everywhere-blank tape. |
| 7 | `bufferTape_nat` · 452 | At a nonnegative integer represented by a natural `i`, the tape is exactly optional list lookup `w[i]?`, including out-of-range blank. |
| 8 | `bufferTape_left` · 456 | Cell `−1` of every word's buffer is blank. |
| 9 | `bufferTape_append` · 464 | Appending `b` changes precisely integer cell `w.length` to `some b`; all other cells retain their previous values. |
| 10 | `VirtualTag` · 482 | A Boolean tag is false at native position `0` and true at position `n+1`; no condition is imposed at positions `1,…,n`. |
| 11 | `virtualMove` · 487 | Replaces a requested left move by stay when reading blank with a false tag, and a requested right move by stay when reading blank with a true tag. In every other case it returns the requested move. |
| 12 | `virtualNextTag` · 492 | After an actual left move the new tag is false; after an actual right move it is true; after stay it retains the old tag. |
| 13 | `bufferTape_inputSymbol` · 499 | For every configuration on word `w`, reading the buffer at integer cell `c.inputPos.val − 1` equals its native input read. No run-reachability assumption is required. |
| 14 | `virtualMove_correct` · 518 | For every configuration, valid tag, and requested move, adding `virtualMove` to physical position `c.inputPos.val − 1` gives exactly the clamped native successor position minus one. Updating the tag using that actual move preserves `VirtualTag`. Both conclusions hold even for arbitrary starting configurations. |
| 15 | `bufferedCompTM` · 566 | Builds a Boolean machine with `M₁.k + 1 + M₂.k` work tapes. It first runs `M₁`, suppresses real output, and appends each emission to the middle tape; even `M₁`'s halted state becomes a live administrative state. It then takes a left step, scans left to blank, steps right, and starts `M₂` with tag true. The second phase reads its virtual input from the immutable middle tape, clamps virtual moves using the tag, runs on the right block, and sends its emissions to real output. Only the second phase can set the composite state to `none`. |
| 16 | `bufferedFirstCfg` · 596 | Embeds any first-machine configuration with state `some (.inl c.state)`, preserving its native input and left work block, putting its emitted word in the buffer with head at its length, and leaving the right block blank and real output empty. A halted first configuration is therefore embedded as live. |
| 17 | `bufferedFirstCfg_init` · 606 | The composite's initial configuration equals this embedding of the first machine's initial configuration. |
| 18 | `bufferedFirstCfg_step` · 627 | From a live first-machine configuration, one composite step is exactly the embedding of one first-machine step. The successor is allowed to be halted, so its last emission is included. The lemma does not assert lockstep from an already halted first configuration. |
| 19 | `bufferedFirstCfg_run` · 672 | The preceding correspondence holds for `t` steps provided every source configuration at times `s<t` is live. The source may halt exactly at `t`. |
| 20 | `bufferedSecondCfg` · 686 | Embeds a second-machine configuration on virtual word `y` into the composite on physical input `x`: it retains arbitrary frozen native input position and left block; stores `y` in the middle tape with head `c.inputPos.val−1`; copies the second work block and output; and maps live states to tagged second-phase states, preserving actual halting. No tag-validity condition is built into this definition. |
| 21 | `bufferedSecondCfg_step` · 702 | With a valid initial tag, one composite step equals the embedding of one second-machine step for some successor tag satisfying `VirtualTag`. The frozen input position and left block are unchanged. There is no liveness premise, so the absorbing halted case is included. |
| 22 | `bufferedSecondCfg_run` · 755 | The same assertion holds at every finite time `t`, existentially returning a valid final tag. It does not assert the same tag throughout the run. |
| 23 | `bufferedScanCfg` · 773 | Constructs a live scan state with immutable word buffer and middle head `j−1`, arbitrary frozen physical input/left block, blank right block, and empty output. The definition permits every natural `j`; a bound is required by the next lemma. |
| 24 | `bufferedScanCfg_run` · 790 | If `j≤y.length`, exactly `j+1` steps from that scan configuration produce the tagged embedding of `M₂`'s initial configuration on `y`, with tag true and all frozen data retained. |
| 25 | `bufferedFirstCfg_rewind` · 844 | If the embedded first configuration is halted, exactly `c.output.length+2` composite steps start the second machine on that output, with tag true and the first input position/work block retained. |
| 26 | `bufferedComp_start` · 873 | Given `M₁.ComputesInTime x y t₁`, there exists a time `a≤t₁+y.length+2` and some frozen input position/left tapes/heads at which the composite is exactly the initial second-phase embedding on `y`. This is a prefix-start statement; it does not by itself assert completion of `M₂`. |

The subsequent docstring comparison found no mismatch in these 26 declarations. In particular, the liveness premise of the first-phase lemmas and the tag premise of the second-phase lemmas must remain part of their shared interfaces.

## Findings

**No mathematical blocker or major was found in the inspected epoch-2 surface. Three minor documentation/tooling findings remain.** This is not a blanket approval or an independent Lean build certificate: the four admissions remain, and the merged elaboration and axiom footprints were not rerun here. Each conclusion below has its own scope.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Robustness/AlphabetReduction.lean` · module “Deviations” paragraph, lines 29–38; `arCode`; `alphabet_reduction` appendix | The simulator block-encodes work symbols in logarithmic width. | The module description still unqualifiedly says `⌈log₂ Γ.card⌉` bits, while `arCode` uses width `Fintype.card Γ + 1`. The theorem appendix correctly and explicitly discloses the actual construction. For `Γ = Bool`, the delivered width is 3 and its per-step constant is 11, not the width-1 implementation described at the top. This is a prose inconsistency, not a defect in the existential theorem. | Add a module-level implementation clarification or identify logarithmic width as the original sketch; cross-reference the one-hot appendix. Preserve the theorem statement. |
| 2 | minor | Audit brief · attestation 4, new-import inventory | New imports across the fills are only precise `Mathlib.Data.Fintype.*` modules. | The independent pre-fill diff also adds `Mathlib.Tactic.Ring` in alphabet reduction, and `Mathlib.Tactic.DeriveFintype`, `Mathlib.Data.List.FinRange`, and `Mathlib.Data.Sigma.Basic` in SingleTape. These are precise imports and are not themselves soundness problems. The scoped option and absence-of-bypass source assertions withstand inspection. | Correct the import inventory; retain the distinction between elaboration machinery and proof-checking bypasses. No theorem repair is indicated. |
| 3 | minor | `scripts/style_lint.py` · `DECL_RE` and declaration tally | Its informational public/private counts describe actual Lean declarations. | Running the pinned script reports **3 public / 75 private** in `SingleTape.lean`. One alleged public declaration is the phrase **`lemma advances`** inside the docstring at line 1187. The actual source has two public theorems and 75 private declarations. This does not invalidate its zero-FAIL result for the checks it actually implements. | Strip nested Lean comments before counting, or use an elaborated declaration inventory. Keep the lint's policy claim limited to its documented mechanical checks. |
| 4 | note | `StateRenaming.lean`; `Finite.lean`; refactored imports | State transport and the two completed-run promotions retain the intended hypotheses. | `Action.mapState` is verbatim the old public definition. Action/configuration mapping accepts any function; whole-machine relabeling requires an equivalence and uses its inverse. The initialized-run lemma really starts both machines from their own initial configurations. `computesInTime_iff` removes only the redundant space witness; `Computes.exists_computesInTime_iff` retains totality. The 63 old public declarations in refactor-affected source files were all located with unchanged headers. | Endorse these interfaces as inspected. Do not generalize machine relabeling to arbitrary state maps without a transition-compatibility hypothesis. |
| 5 | note | `Simulation.lean` · all 26 new declarations; `bufferedCompTM`; `Composition.lean` · both fills | Buffering, virtual clamping, guarded composition, and constant 2 handle halting emissions and empty words. | A Boolean interior cell is `some b`, including `some false`, so an interior tag cannot trigger suppression. Boundary tags are preserved by actual movements, including suppressed/stationary ones. Phase-one halting stays live after applying its last action. The mandatory initial left move plus scan/dispatch costs exactly `y.length + 2`. The explicit empty-input traces and time inequalities below meet the adversarial cases. | No statement repair found. Retain the three-block layout, distinct live administrative states, actual-move tag update, and stated premises when reusing the layer. |
| 6 | note | `Robustness/SingleTape.lean` · `sweepTM`, `readVisit`, `writeVisit`, `source_bounds`, `sweepTime` | The delivered two-sweep controller implements both head directions, including guard blocks, within the stated quadratic budget. | Marked blank, boundary, and physical blank are three distinct constructor forms. The forward pass saves the old left-neighbor flag; the return control saves the old right-neighbor flag before replacing a mark. Guard blocks exist on both sides before the return pass. `source_bounds` supplies their blankness and containment. The allocated interval grows to `[-t,t]` even when the source never moves. The independently summed ledger is given below. | No construction defect found. Describe this as an allocated simulation zone, not the exact set of source-visited cells. Keep the separate zero-tape branch. |
| 7 | note | `Robustness/Bidirectional.lean` · `foldPack`, `foldMove`, `foldTM`, `foldSafe`, `nonnegative_heads` | One initialization step plus lockstep simulation yields constant 1 and nonnegative heads on every input. | The two optional payloads are independent; only an untagged pair of blanks packs to physical blank. Origin tags survive erasure. Crossings between virtual 0 and −1 are stationary. `foldSafe` ranges over arbitrary enlarged-alphabet inputs, excludes reinitialization, and preserves correct origin flags. Invalid first input initializes tags and halts; later invalid reads halt without moving. | No repair found. Keep the universal safety proof separate from embedded-input functional correctness. |
| 8 | note | `Robustness/AlphabetReduction.lean` · `arTM`, `arCfg_run`, `arEmission_in_image`, `alphabet_reduction` | One-hot coding and a total output decoder suffice for the literal theorem, including zero tapes. | Blank is the all-`none` block; nonblank codes use `some` bits. Signed block addressing covers negative cells. A live source step costs `L + 1 + L + L + 1 = 3L + 2`, even for zero tapes. `arEmission_in_image` uses append-only prefixes and halt absorption. The final proof instead maps the entire output through `arBit`; its left-inverse law on `e`'s image is sufficient. The image lemma need not be a dependency of that proof. | Accept the disclosed implementation deviation within the theorem's existential constant; apply only the prose fix in finding 1. Do not infer a logarithmic alphabet-dependent constant from this implementation. |
| 9 | note | Four remaining admissions; `Universal.lean` startup sketch | The remaining declarations and sketches survive the merge; the new API supports the next constructions. | `Oblivious.lean`, `Encoding.lean`, and `Universal.lean` are byte-identical to their pre-fill versions. Exactly four source admissions remain. The canonizer can now use proved timed/guarded composition. Universal startup still needs a prefix-only extraction/canonization invariant preserving the unread suffix: the final-output composition theorem alone does not prove that startup costs are independent of the suffix length. This is an implementation obligation of the retained sketch, not a counterexample to the evaluator statement. | Preserve all four statements. Implement the local obligations in the remaining-declarations table below; in particular, do not copy or scan all of `x` before evaluating a fixed code on `x`. |
| 10 | note | Attestation 3 · `UC_not_computable`, normal forms, evaluator-dependent corollaries | The listed axiom footprints establish the advertised proof status. | The source dependency paths agree with the attestation: the five fills and normal-form chain contain no admissions; the three listed residual carriers use `universal`. However, the axiom prints were not independently rerun. Also, `UC_not_computable` has parameter `c : MachineCode`; it is an admission-free theorem **for a supplied scheme**. Producing a concrete effective scheme through the current existence theorem still uses its admission. | State the axiom conclusion at the declaration level and keep the scheme-existence obligation explicit. Do not treat this audit as a fresh kernel certificate or as removing `exists_effectiveMachineCode`. |
| 11 | note | Attestations 2, 5, 6; verification scripts and delivery reports | Build, policy, and delivery claims are independently reproducible from this packet. | Source identity, freeze, import order, source scans, and the 24-file style result were independently checked. The strengthened checker rejects a crashing compiler, missing fresh output, and an `error:` diagnostic. The packet contains reports, not the merged raw build/axiom logs or the original three patches/bundles/manifests. Archive provenance and kernel execution therefore remain attestations. The 1315-line exception is explicitly escalated in batch B and accepted by the maintainer. | Preserve that evidence distinction. If independent build/provenance replay is required at a later gate, attach the actual logs and delivery integrity material. Split the reusable sweep layer during coordinated promotion, rather than expanding `Simulation.lean` indiscriminately. |

## Construction checks and adversarial instantiations

These are mathematical checks of definitions and finite executable spot checks, not replacements for Lean's kernel checking.

### Buffered composition

For a word of length `n`, the virtual position `p` corresponds to integer buffer cell `p−1`. The complete boundary case analysis is:

| Native position | Read | Required tag | Requested moves that are suppressed |
|---|---|---|---|
| `0` | `none` | `false` | Left only |
| `1,…,n` | `some` word symbol | Either | None |
| `n+1` | `none` | `true` | Right only |

In each row, a nonstationary actual move updates the tag to its direction; a stationary actual move leaves it unchanged. Entering the left boundary can only occur by a left move, and entering the right boundary can only occur by a right move. For `n=0`, the first and last rows describe distinct adjacent cells −1 and 0; there are no interior positions. Thus both the position equation and tag preservation in `virtualMove_correct` hold without a reachability restriction on the source configuration.

On a first-machine emission, `a.output.map some` is the optional write `some (some b)`, not a no-write or an erase. The old buffer head is at the emitted prefix length, so `bufferTape_append` gives the new prefix and moving right puts the head on its new right blank. The successor state is `some (.inl a.state)` even when `a.state = none`.

A fully specified adversarial example uses zero work tapes in each component. The first machine's only transition emits `false` and halts; the second machine's only transition emits `true` iff its input read is `some false`, otherwise emits `false`, and halts. Both input moves are stationary. On `x=[]`:

| Composite time | Phase | Buffer head | Real output |
|---:|---|---:|---|
| 0 | First machine live | 0 | `[]` |
| 1 | First machine's halt represented by live administration | 1 | `[]` |
| 2 | Scan, reading the emitted `false` | 0 | `[]` |
| 3 | Scan, reading left blank | −1 | `[]` |
| 4 | Second machine initialized, tag true | 0 | `[]` |
| 5 | Composite halted | 0 | `[true]` |

If the first transition instead halts without emitting, the administrative path is buffer head `0 → −1 → 0`; the second phase starts at time 3, with its virtual input position 1 correctly tagged as the right boundary of `[]`. If the first machine loops forever, even while emitting, its embedded state remains live and real output remains empty. If only the second machine loops, its `Option.map` state remains live. These observations address both divergence directions of guarded composition, not just the successful path.

With `n=x.length`, `y=f x`, and source halt times bounded by `T₁(n)` and `T₂(y.length)`, the timed calculation is

\[
\begin{aligned}
y.\mathrm{length}&\le T_1(n),\\
\mathrm{time}
&\le T_1(n)+y.\mathrm{length}+2+T_2(y.\mathrm{length})\\
&\le 2T_1(n)+T_2(T_1(n))+2\\
&\le 2\bigl(T_1(n)+T_2(T_1(n))+1\bigr).
\end{aligned}
\]

Only the second inequality uses monotonicity of `T₂`. No monotonicity of `T₁` or full scan of `x` is needed.

### One-work-tape sweep

The three distinguishing representations are

```lean
none                                           -- physical blank
some (Sum.inr none)                             -- boundary
some (Sum.inr (some (i, none, true, false)))      -- marked source blank
```

For any source action `a`, tape `i`, and source coordinate `j`, the desired new head flag is

\[
\operatorname{headAt}(a.\operatorname{apply}(c),i,j)=
\begin{cases}
\operatorname{headAt}(c,i,j+1),&a.\mathrm{workTapes}(i).2=-1,\\
\operatorname{headAt}(c,i,j),&a.\mathrm{workTapes}(i).2=0,\\
\operatorname{headAt}(c,i,j-1),&a.\mathrm{workTapes}(i).2=1.
\end{cases}
\]

`readVisit` saves the third case's old flag in the cell before any old head flag is changed. `writeVisit` returns the **old current** flag into control, so the next cell to the left sees exactly the first case's old right flag. It never propagates an already moved mark a second time. At the new right guard, the carried right flag is false and the saved left flag comes from the old right edge; at the new left guard, the carried right flag comes from the old left edge and its saved left flag is false. Thus outward moves at both old edges land in the fresh guards.

`source_bounds` starts from head position zero and blank work tapes. After each source step, heads move by at most one and the only possible write is at the previous head. Induction therefore confines heads and nonblank support to `[-t,t]`. This is containment, not equality with the visited set. A stationary source still causes the simulator to grow one block at each end of every live macrostep.

For `k>0`, initialization uses `k` origin writes, one boundary/turn step, `k` return steps, and one left-boundary write: `2k+2`. With `n` old blocks, a macrostep uses

\[
k+1+(n+1)k+1+k+1+(n+2)k+1=(2n+5)k+4.
\]

Substituting `n=2t+1` and summing gives

\[
\begin{aligned}
S_k(t)
&=2k+2+\sum_{s=0}^{t-1}\bigl((4s+7)k+4\bigr)\\
&=2k+2+2kt(t-1)+(7k+4)t\\
&=2kt^2+(5k+4)t+2k+2,\\
(9k+6)(t+1)^2-S_k(t)
&=(7k+6)t^2+(13k+8)t+7k+4\ge0.
\end{aligned}
\]

This ledger applies through the source's first halt. After the composite halts, absorption replaces further sweeps. For first halt `τ≤T(n)`, the budget is consequently at most `(9k+6)(T(n)+1)²`. At `k=0`, `unusedTapeTM` instead preserves every input/output step and leaves one added tape blank and stationary; `T(n)≤(T(n)+1)²` permits constant 1.

### Fold safety and initialization

`foldPack (false, none, none) = none`, but `foldPack (true, none, none) = some (true, none, none)`. Consequently erasing both source payloads cannot erase an origin tag. A write changes only its selected optional payload.

The critical crossings are exact:

\[
\begin{aligned}
\operatorname{foldPos}(0)&=\operatorname{foldPos}(-1)=0,\\
\operatorname{foldMove}(\mathrm{true},\mathrm{true},-1)&=(0,\mathrm{false}),\\
\operatorname{foldMove}(\mathrm{false},\mathrm{true},1)&=(0,\mathrm{true}).
\end{aligned}
\]

At physical position zero, no case returns a negative move. At a positive integer position, every move is at least −1, so the next position remains nonnegative. `foldSafe` supplies the correct origin flag at the current cell for **any** component-side bit and any enlarged-alphabet input. Its initialization lemma quantifies over arbitrary input words, not only `x.map foldEmbedding`. Time zero has all heads at zero; after one initialization step safety holds, including when that step halts on a malformed first symbol; safety then persists by induction and halt absorption. This discharges case A14 without using the functional computation premise.

On embedded inputs, `foldCfg_run` gives exact correspondence at time `t+1`. Hence

\[
1+\tau\le1+T(n)=1\cdot(T(n)+1),
\]

including `n=0`. Zero tapes make the head conditions vacuous; an empty source alphabet introduces no missing inhabitance assumption.

### Alphabet reduction and remaining small cases

`arCode` distinguishes blank from every nonblank code: blank has only `none` cells, while a nonblank code consists entirely of `some` bits and has its distinguishing true bit at the finite index of the source symbol. The extra last coordinate is harmless. For width `L=Γ.card+1`, physical coordinates use Euclidean division by positive `L`, so negative source cells are represented as well.

Every live macrostep performs `L` reads, one dispatch applying native input motion and emission, `L` writes, `L` moves, and one final state transition. Thus its cost is exactly `3L+2`; there is no initial blank-tape encoding pass. Optional no-write is normalized to writing back the old read, while explicit blank-write stays an erase. At zero tapes the loops remain finite control transitions, giving the same positive bound. For `Γ=Bool` and `e=id`, the construction is an 11-step-per-live-step simulator; the theorem does not promise identity or optimal slowdown.

If a source symbol `γ` is emitted at step `t<T(n)`, append-only output gives

\[
\gamma\in\mathrm{output}(t+1),\qquad
\mathrm{output}(t+1)\preceq(f(x)).\mathrm{map}(e),\qquad
\gamma\in\operatorname{range}(e).
\]

If `t≥T(n)`, halt absorption makes such an emission impossible. Thus `arBit`'s arbitrary behavior outside the image cannot change a promised binary computation. Independently, the exact run map transforms all output by this total decoder, and `arBit(e b)=b` recovers the final word.

For all five target theorems, a computation premise with an identically zero bound is impossible: instantiate it at the empty input and use `not_computesInTime_zero`. More generally, a zero bound at any **attained** input length is impossible. For an empty source alphabet, positive lengths need not be attained; this qualification avoids introducing a false universal positivity claim about `T`.

The finite executable checks enumerated all Boolean words through length 8: **24,582** valid position/tag/move cases, **511** rewinds, and **1,022** append updates. They also checked **36,864** local sweep configurations with one or two tapes, radii 0–3, all allowed head positions, all directions, no-write/erase/write choices, and blank/nonblank payload patterns; **387** signed fold movements; **108** packing/write cases; and one-hot codes and signed block coordinates for alphabet sizes 0–8. All passed. These checks use independent Python expressions derived from the definitions and are bounded checks, not Lean executions or general proofs.

## The four remaining admissions

| Declaration | Freeze check | Literal obligation and next-phase assessment |
|---|---|---|
| `oblivious_of_mem_DTIME` · `Oblivious.lean:109` | Entire module unchanged from `60bdab6b`; also unaffected by the refactor. | Produce a binary decider with equal-length input/work-head trajectories and quadratic padded budget. The corrected masked-clock, input-copy, parked-native-input, fixed-layout, padded-sweep construction remains implementable. The new sweep rules can help, but `one_work_tape` alone does not prove obliviousness, and early source halting must not stop the prescribed physical schedule. Fixed-duration binary coding still needs its own trajectory argument. |
| `exists_effectiveMachineCode` · `Encoding.lean:455` | Declaration and sketch unchanged; entire module unchanged since pre-fill. | Supply a total padded decoding scheme plus an actual machine computing scheme-independent serialization. The finite parser can short-circuit malformed, truncated, or impossibly large claimed tables. Proved timed composition now combines total parsing/reserialization machines with monotone polynomial bounds; guarded composition supports partial stages where needed. Neither result constructs the parser automatically, and no appeal to `universal` is needed or appropriate. |
| `universal` · `Universal.lean:102` | Entire module unchanged since pre-fill; refactor did not change it. | One fixed evaluator per scheme, all codes, code-dependent linear overhead, and converse completed-output correctness. Read only the code prefix, run/capture its canonizer output, retain the suffix start, and simulate the suffix lazily with a left-boundary marker. Buffered first-phase invariants and inactive native-input preservation support this design; add explicit prefix-start and captured-table correspondence lemmas. The compound input is not just a buffered whole word, so the whole construction is not discharged by `computesFunInTime_comp` alone. |
| `timed_universal` · `Universal.lean:165` | Entire module unchanged since pre-fill; refactor did not change it. | Extend an explicit interpreter with a counter of **source transitions**, buffered output, inclusive deadline checking, and tagged success/timeout output. It cannot be obtained merely by giving an arbitrary black-box evaluator a wall-clock cutoff. The retained sketch correctly extends the interpreter; `t=0` times out and a first halt at exactly `t` succeeds. Counter and flush costs fit the padded quadratic budget. |

These are outline-level assessments of outstanding implementation work, not proofs of the admitted declarations.

## Attestations 1–6: evidence disposition

| Attestation | Independent result |
|---|---|
| 1 — freeze | **Reproduced at source level.** All 24 extracted Lean files match their Git blob hashes at the pinned head. The pre-fill diff removes exactly ten source lines: five admissions and five docstring closing lines, whose preceding text is retained before appended notes. All old public headers in the compared refactor files remain; `Action.mapState` is verbatim. The intervening `24687122 → 60bdab6b` commit changes only the plan and briefs, not Lean sources. The three remaining-admission files are unchanged from pre-fill. |
| 2 — elaboration | **Not rerun.** Lean/Lake are unavailable in this audit environment. The pinned files specify Lean 4.25.0 and mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The checked 24-entry module order exactly matches the packet's Lean inventory and orders every chapter import correctly. Four source `sorry`s remain. These are not substitutes for fresh elaboration or warning counts. |
| 3 — axioms | **Maintainer-attested; source dependencies consistent.** No independent `#print axioms` execution. Batch B/C reports' admitted binary corollary is expected at their separate bases and is consistent with the merged attestation removing both underlying admissions. `universal_quadratic`, `UC_computable_of_HALT_computable`, and `HALT_not_computable` retain their visible dependency on `universal`; none of their displayed proofs invokes the scheme-existence admission. See finding 10 for the conditional scheme parameter. |
| 4 — soundness scan | **Source scan reproduced, with import erratum.** No `axiom`, `admit`, `native_decide`, `implemented_by`, `extern`, or `unsafe` token occurs in the comment-stripped chapter sources. The only `sorry` tokens are the four declared admissions. The new `synthInstance.maxSize 8192` is scoped to the one equality instance and increases elaboration search capacity; it does not disable kernel checking. `derive_fintype%` builds a finite-control instance. The assertion restricting all new imports to `Fintype.*` is incorrect (finding 2). |
| 5 — policy | **Mechanical campaign result reproduced:** zero FAIL, one WARN over all 24 attached Lean files, with the WARN at 1315-line SingleTape. Every remaining admission has its sketch and chapter facades cover the attached children. Batch B explicitly requests later extraction and explains its one-file ownership restriction. StateRenaming now has References. The three legacy NPReductions failures were not rerun because those files are outside the packet and scope. The linter's informational count defect is finding 3; zero FAIL does not certify policy conditions it does not implement. |
| 6 — provenance | **Partially corroborated, not replayed.** The reports consistently name base `24687122`, disjoint ownership, and their separate remaining-admission counts. Batch B's reported full-source SHA-256 matches the attached and pinned source exactly. The original three archives, format patches, Git bundles, manifests, and raw logs are absent from this packet; their mutual consistency, authorship preservation, and the maintainer's separate runs are not independently certified here. |

The strengthened shell checker was tested with an isolated stand-in compiler. A nonzero exit (23), a zero exit without a fresh output despite a pre-existing stale file, and a zero exit with an `error:` diagnostic each yielded checker exit 1. A zero exit with a new nonempty output and no diagnostic yielded exit 0. This tests the historical gate conditions; it is not a Lean compilation.

The packet has exactly its advertised 36 attachments. It does not attach the 2009 book PDF. The source-model comparison in this delta audit therefore uses the supplied corrected phase-2 audit designs and frozen source-deviation statements; it does not claim a fresh certification of the published book's pagination or reopen those closed convention choices.

## Promotion recommendations for the epoch-3 merge

Batch A requests no additional shared lemmas. For B and C, endorse the following small raw interfaces and keep controller-specific representations private. These are recommendations, not edits made by this audit.

1. **C's optional-write normalization:** promote `arUpdated_tape`, preferably at the raw configuration/action layer and re-export it through Simulation. Its statement should remain

   ```lean
   (a.apply c).workTapes i =
     Function.update (c.workTapes i) (c.workTapePos i)
       ((a.workTapes i).1.getD (c.workTapeSymbols i))
   ```

   for arbitrary alphabet/state, action, configuration, and tape index. No finiteness, liveness, or computation hypothesis is needed. A name such as `Action.apply_workTapes` reflects its scope. The no-write case updates a cell with its existing value; explicit `some none` remains a blank write.

2. **B's head/support bound:** promote `source_bounds`, generalized from `FinTM` to the raw `MultiTapeTM` if useful. Retain both conclusions at every initialized time: every work head lies in `[-t,t]`, and every cell outside that interval is blank. Require initialization on blank work tapes; do not silently assert the support conclusion for arbitrary starting configurations. This is immediately useful for universal/oblivious allocation.

3. **B's generic sweep/zipper layer:** endorse extraction to a separate raw sweep module, rather than adding hundreds of lines to the already 896-line Simulation module. Preserve the current statements of `sweepTape`, `sweepCfg`, `sweepRevCfg`, their local write/move/turn identities, `sweepFold`, `sweep_run`, `sweep_run_reverse`, and `sweep_generate`. In particular, retain the local transition-table hypothesis of each run lemma, arbitrary inactive input/output, exact scanned-word-length cost, and full resulting configuration; do not replace those with a mere output-correctness conclusion. Coordinate/list extents are proof parameters, not unbounded controller fields.

4. **B's indexed finite transducers:** promote `indexedVisit`, `indexedFold`, and its forward/reverse complete-block specializations together with that sweep layer. Preserve `is.Nodup` in the general lemma: two visits to the same index can change the control twice, so its conclusion using the original entry would fail without distinctness.

5. **B's unused-tape embedding:** sound but lower priority unless epoch 3 needs it. If shared, expose same-alphabet zero-to-one-tape configuration lockstep, and the useful exact consequence

   ```lean
   (unusedTapeTM M hk).ComputesInTime x w t ↔ M.ComputesInTime x w t
   ```

   with `hk : M.k = 0`, for every `x`, `w`, and `t`, rather than only a total-function implication. The added tape is always blank with head zero. This strengthens the convenience API without assuming totality or changing the construction.

Do not promote `SweepState`, `sweepTM`, the particular neighbor-flag payload, fold safety internals, or the one-hot controller merely because they are large. Their public consumers need the generic local/run interfaces above; any new or generalized public statement should receive its own statement check.

## Notation glossary

Lean identifiers retain their meanings in the attached sources. `x` is the original input, `y` an intermediate word, `w` a generic word, and `n` an input/word length (or the explicitly local old-block count in the sweep ledger). `M`, `M₁`, and `M₂` are machines; `c` is a configuration in the construction checks or the explicitly typed coding scheme in the theorem discussion; `a` is a source action. `Γ` is a source alphabet, `e` its input/output embedding, `γ` an emitted source symbol, and `b` a bit. `k` is the source work-tape count, `i` a tape index, `j`/`z` integer tape coordinates, and `p` a native input position or explicitly designated physical coordinate. `t`/`s` are step numbers, `τ` a first halting time, `T`/`T₁`/`T₂` time bounds, `S_k(t)` the sweep time through `t` source steps, and `L=Γ.card+1` the delivered block width. `≼` denotes list prefix; `range(e)` is the image of the embedding. Any asymptotic constant discussed for a remaining sketch may depend on its fixed machines and, for universal simulation, the fixed code, but not on the suffix input length.
