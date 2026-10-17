External audit of PR #117 (MIG-11a), statement gate

Audited the supplied `mig11a-bundle.md`, containing 39 distinct sections. Its SHA-256 is exactly `84d0442fccfaea170d4428fe01d71fb16fe31ff50f615e2229a818925551b99b`.

The four row contracts faithfully package their framed theorems and supply the missing leaf contracts identified for MIG-12. I found two minor issues, neither affecting the correctness of the four instances or preventing the planned migration.

This is a source-and-packet audit. I independently checked the patch, source signatures, lint, duplication screens, and consistency of the supplied logs. Lean and the complete dependency tree are not installed here, so elaboration and kernel-axiom results below are supplied evidence, not a fresh Lean run by this auditor.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Build/Contract/Counter.lean` · `counterRowContract`, docstring at lines 41–48 | The generic constructor does not require its word map to preserve width, although the docstring describes it as width-preserving and its endpoint as holding `v`. The formal endpoint only writes `bufferTape v` within the old word's interval. | Neither the parameters nor `hrun` require `v.length = w.length`. Take `fix [] = some [true]`, `fix (_ :: _) = none`, `lead = id`, and a machine making two stationary transitions `run → rewind true → done true`. This satisfies every clause of `hrun`, yet the successful pair has lengths 0 and 1; no cell is written. The complete clause check appears below. The actual increment and decrement instances preserve width and are unaffected. | Describe the generic endpoint as writing `bufferTape v` within the interval of length `w.length`; reserve width preservation for the two instances. Alternatively, require the length property if it is intended as part of the generic interface. A documentation correction suffices. |
| 2 | minor | `audits/evidence/mig11a/logs/lint-head.txt` · final-source provenance; `NOTES.md` · lint attestation | The supplied lint log does not describe the final counter module. | The log reports 122 lines and 2 public declarations for `Contract/Counter.lean`. The bundled file, matching patch blob `e19cd9b1`, has 131 lines and 3 public declarations, including `counterRowContract`. Running the supplied linter on that final file gives 0 FAIL, 0 WARN, and the correct tally. | Regenerate the full lint log at the recorded final head and record that commit with the result. Preserve the original evidence and acknowledge the stale entry in the resolution record. |

The seven brief questions are answered as follows.

1. **Faithfulness.** The preconditions, times, endpoints, cuts, and envelopes agree with the wrapped framed theorems. The following are restatements of the six new definitions from their formal declarations. In every contract, the start must separately have its declared entry state; this is supplied to `Contract.run`, `cut`, and `env`, rather than repeated inside `pre`.

| Definition | Mathematical content |
|---|---|
| `compareStop u v` | The length of the initial segment of `zip u v` whose paired symbols agree. It stops at the first unequal symbol pair or when either word ends. |
| `copyTM_contract src dst hne x` | Index `w`. Require the source tape to contain `w`, with blank delimiters at offsets `-1` and `w.length`. From `sweep`, reach `done` after exactly `2 * w.length + 2` steps. Replace only the destination cells from its initial head through offset `w.length - 1` with `w`; retain every other cell. Both selected heads stay between their initial position minus 1 and their initial position plus `w.length`; every other head is fixed. The exit set is the singleton `done`, excluded at every earlier time. |
| `compareTM_contract fst snd hne x` | Index `(u,v)`. Require both delimited words at their respective heads. From `run`, reach `done (decide (u = v))` after exactly `2 * compareStop u v + 2` steps, with the entire initial configuration unchanged except its state. Both selected heads stay between their initial position minus 1 and their initial position plus `compareStop u v`; all other heads are fixed. Both verdicts are exits, and neither occurs earlier. |
| `counterRowContract M i x fix lead hrun` | Index `(w,v)`. Require `fix w = some v` and delimited `w` at tape `i`. From `run`, reach `done true` after exactly `2 * (w.takeWhile lead).length + 2` steps. On tape `i`, replace the old word interval using the corresponding cells of `bufferTape v`; preserve everything outside that interval. The selected head stays between its initial position minus 1 and its initial position plus `(w.takeWhile lead).length`; other heads are fixed. Both verdicts are exits, and neither occurs earlier. All guarantees are supplied by the assumed framed theorem `hrun`; no length equality is separately imposed. |
| `incrementTM_contract i x` | The preceding constructor with `M = incrementTM k i`, `fix = incFixed`, and `lead = id`. Its domain is successful fixed-width increments; its scan length is the number of leading `true` bits. |
| `decrementTM_contract i x` | The preceding constructor with `M = decrementTM k i`, `fix = decFixed`, and `lead = not`. Its domain is successful fixed-width decrements; its scan length is the number of leading `false` bits. |

All four row endpoints restore the complete work-head vector and preserve the input position and output. Copy requires no destination blankness or destination delimiter: the stronger source-only precondition is exactly that of `copyTM_run_ofCfg`. `copyTM_contract_frames` gives preservation outside the destination interval; it is an endpoint frame, not a claim about every intermediate tape configuration.

The stop characterization is the correct one:

\[
\begin{aligned}
&\forall r<\operatorname{compareStop}(u,v),\quad
  \exists b:\ u[r]?=\operatorname{some}(b)\ \land\ v[r]?=\operatorname{some}(b),\\
&\neg\exists b:\ u[\operatorname{compareStop}(u,v)]?=\operatorname{some}(b)
  \ \land\ v[\operatorname{compareStop}(u,v)]?=\operatorname{some}(b).
\end{aligned}
\]

In particular, two simultaneous blanks satisfy the second clause; it does not incorrectly require the two optional cells to differ. The private `catalog_compare_stop` supplies these same two clauses for its witness. `compareStop_unique` therefore identifies that witness with `compareStop`. The exact-time theorem retains the private trace's endpoint, both-verdict cut, and head bounds at that witness. The old existential theorem follows by choosing `compareStop` and using `compareStop_le`.

2. **Design.** The range of both verdicts is appropriate. Its cut rules out premature dispatch at either flag; a singleton containing only the eventual verdict would not express that requirement. The successful counter contract still guarantees `done true` through its endpoint equation: membership of `done false` in the exit set does not promise an overflow case. The pair `(w,v)` gives a total endpoint function while the precondition restricts it to successful computations. For fixed `w`, functionality of `fix` makes an admissible `v` unique. The shared counter constructor factors the common contract packaging without duplicating the arithmetic trace. Keeping it in `Contract/Counter`, importing `CounterLoop`, avoids introducing that dependency into `Contract/Catalog`; the facade imports and documents the new module.

3. **Coverage for MIG-12.** The four missing row names are correct. In the supplied `CfgRecord`, their actual theorem call sites are: copy twice (lines 1779 and 3474), compare once (4804), increment once (2924), and decrement once (2923). The design note's larger counts for some rows include prose mentions; they should not be read as counts of executable proof references. The arithmetic transport explicitly supplies the success equation and `v.length = w.length`; its current uses require neither overflow nor underflow contracts.

No further leaf-contract field is missing for the stated migration. Compare's empty-footprint frame follows from `compareTM_contract_post` and `Contract.frames_iff`. The counter frame follows from its `_post` equation, `Contract.frames_iff`, and the existing interval-preservation argument. These derivations do not require unfolding another file's definition. Named `_frames` lemmas would be convenient, but their absence does not hide necessary information. `RecordRun` only requires a coordinatewise common radius; the contract envelopes, `Contract.segment`, and `Segment.mono` provide it. It does not require a stronger relation between moving heads. The counter-loop escape phase remains the explicitly declared MIG-15 exception. This checks the proposed inputs to MIG-12, not the as-yet unwritten migration itself.

4. **Definitions with lemmas.** `compareStop` has its defining equation, recursion on two nonempty words, characterization, uniqueness, and length bound. Its defining equation also covers empty inputs. Each of the five contract-valued definitions has all five data-field equations (`pre`, `time`, `post`, `lo`, `hi`): the supplied probes print 10 equations for copy/compare and 15 for the counter constructor and instances. Copy's endpoint equation intentionally retains `sweepPost`, whose field equations are already published in the same module. All new `simps` registrations specify `isSimp := false`; the patch adds no `@[simp]`, axiom declaration, or `sorry`. The docstrings describe the mathematics, subject to finding 1. Independently rerunning lint on the eight bundled Lean files gives 0 FAIL and 9 existing WARN; check 8 adds no uncovered definition in either modified existing module, and the new counter module has no warning. This is a scoped rerun, not a reproduction of the complete 79-file lint total.

5. **No behavior change.** After removing only the bundle's Markdown fences, all four modified source files match the Git blob identifiers in `mig11a.patch`. Reversing the patch succeeds; the three reconstructed existing files also match the patch's old blob identifiers. The declaration comparison finds seven added publics in `Build/Catalog`, three in `Contract/Catalog`, and three in the new counter module; no existing public signature or private declaration changes. `compareTM_run_ofCfg` has a byte-identical signature. Its body is the only changed existing declaration body. The facade change is its additional import and documentation. No existing machine transition table or definition changes.

6. **Duplication.** Independently running the supplied v3 screen on the reconstructed base and delivered head reproduces both supplied screen files byte for byte: 549 → 559 screened declarations, 320 → 321 pairs, and 105,754 → 105,830 reproduced characters. The compare pair is the old body under its new exact-time theorem name, with the old pair disappearing. The remaining new pair is 76 characters of the shared `sweepContract` application. It is constructor reuse, not a copied proof family. I found no new duplication requiring human acknowledgment in this patch; this does not reopen or discharge unrelated pre-existing debt.

7. **Records and verification evidence.** The notes accurately describe the final definitions, factoring, field equations, and patch, apart from the stale lint evidence in finding 2. The counter probe starts with the exact final counter module. The two Catalog elaboration logs contain 77 warnings each and are byte-identical after normalizing source locations. The overlay has 77 warnings; the counter probe has none; none of these logs reports an error. The eight printed axiom reports contain only standard Lean axioms, or none; the counter probe prints field signatures rather than additional axiom reports. The replay contains 86 distinct modules in exactly the supplied order, all with `exit=0` and `errors=0`; its admission counts sum to 57. The attached static-count summary agrees with that total. The entire 86-module source tree and the preceding replay are not in this packet, so the claimed full static comparison and unchanged counts on the 85 shared modules remain maintainer attestations. All eight bundled Lean modules themselves contain zero `sorry` tokens after comment stripping.

The following adversarial instances check the boundary behavior. All positions below are relative to the selected initial head; the tests also used negative absolute positions and arbitrary exterior cells.

| Instance | Calculation and expected result |
|---|---|
| Compare `[]` with `[]` | Stop `0`; time `2 * 0 + 2 = 2`; verdict `true`. At times 0, 1, 2 the states are `run`, `rewind true`, `done true`, and both head offsets are `0`, `-1`, `0`. Thus the cut includes time 0 and the lower envelope endpoint is needed. |
| Compare `[false]` with `[true]` | Stop `0`; time `2`; verdict `false`; no tape cell changes. |
| Compare `[true]` with `[true,false]` | Stop `1`; time `2 * 1 + 2 = 4`; verdict `false`. The head offsets are `0,1,0,-1,0`, within `[-1,1]`. |
| Copy `[]` to an arbitrary occupied destination | Time `2`; the destination interval is empty, so every destination cell remains unchanged despite the head visiting offset `-1`. |
| Increment `[true,true,false]` | Result `[false,false,true]`; leading carry length `2`; time `2 * 2 + 2 = 6`; successful verdict and restored head. |
| Decrement `[false,false,true]` | Result `[true,true,false]`; leading borrow length `2`; time `6`; successful verdict and restored head. |
| Empty or exhausted counter | `incFixed [] = none` and `decFixed [] = none`; all-`true` increment and all-`false` decrement also fail their success preconditions. The success contracts assert nothing about those runs. |

As an additional finite check, an independent Python transition model checked all 961 pairs of binary words of length at most 4 for compare, all 31 such words for copy into an occupied destination, and all 57 successful inputs of length at most 5 for each arithmetic row. Exact first-exit time, endpoint contents, restored heads, exterior preservation, and envelopes all passed. These finite checks supplement the statement audit; they are not Lean proofs or universal verification.

For completeness, finding 1's generic counterexample satisfies `hrun` as follows. Set `k = 1`, `i = 0`, `lead = id`, and define `fix [] = some [true]`, with `fix w = none` for every nonempty `w`. Let `M` change only its state, from `run` to `rewind true`, and then to `done true`, remaining there afterwards. Then:

\[
\begin{aligned}
\operatorname{fix}(w)=\operatorname{some}(v)
&\Longrightarrow w=[]\ \land\ v=[\mathrm{true}],\\
2\lvert\operatorname{takeWhile}(\mathrm{id},[])\rvert+2&=2,\\
[d.\mathrm{workTapePos}(0),\ d.\mathrm{workTapePos}(0)+|w|)&=\varnothing.
\end{aligned}
\]

Consequently the prescribed endpoint is just `d` with state `done true`, exactly the actual configuration at time 2. At the only earlier natural times, 0 and 1, the states are `run` and `rewind true`, excluding both exits. Every head stays at its initial position, which lies in the required interval from that position minus 1 through itself. All nonempty inputs have a false success premise. Thus every clause of `hrun` holds, while `v.length = 1` and `w.length = 0`. This refutes the generic width-preservation description, not any Lean theorem or either concrete arithmetic instance.

Notation: `u,v,w` are words; `|w|` is word length; `u[r]?` is optional list lookup; `d` is the starting configuration; `r` is a list index; `b` is a symbol; `M` is a machine; `k` is its work-tape count; `i` is the selected tape; `fix` and `lead` are the constructor's partial word map and prefix predicate. Intervals use their usual inclusive or half-open conventions.

PASS (zero blockers, zero majors; 2 minors, 0 notes).
