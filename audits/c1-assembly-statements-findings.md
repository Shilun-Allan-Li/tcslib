Input SHA-256: `fc27aee38181d7eab8f3989d9c41acb9a5a94afa3153003a2e49519476eb968d` — matches the expected digest. Exactly **53 sections**, counted by the repository-path headers.

**C1-A ASSEMBLY STATEMENT GATE — external audit, 2026-10-14.**

**Verdict: OPEN — 0 blockers, 1 major, 3 minors.** I found no false assembly theorem or missing hypothesis that prevents either supplied consumer derivation. The major is exclusively the construction-reuse policy: the clean-configuration proof repeats existing private embedding glue without a supplied human acknowledgment of that new debt. Close it by supplying and using the small shared capture-field export, or by recording the human acknowledgment and scheduled resolution required by policy §1 and the audit template. The three minors concern prose and verification evidence; none requires weakening a theorem statement.

Scope: the proposed `Build/NDHost.lean` addition, its eight assembly theorems, the core interface, both consumer derivations, landing form, and the pack's four questions. I inspected definition bodies with comments removed before comparing their docstrings. Existing contracts and the consumers' fills remain out of scope. In particular, this report does not certify the writer/core fills or discharge H1's harvest gate.

I regenerated the supplied evidence files and ran independent static and finite-transition checks. **I did not independently run Lean:** no `lean` was available on PATH, and the pinned checkout, olean snapshot, and elaboration wrapper are not supplied. Reported kernel/axiom results remain maintainer execution evidence, checked for consistency with the supplied sources.

**Findings.** “Unit” means `audits/evidence/c1/assembly/C1Assembly.lean.txt`; line numbers refer to extracted source with outer presentation fences removed. Other paths below are repository paths or abbreviated beneath `audits/evidence/c1/assembly/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| M1 | major — policy only | Unit: `guessRunCfg_clean`, lines 724–728, 764–769, 780–785; `Build/Embed.lean`: `embedSlot_unselected`; `SpaceComplexity/Inclusions.lean`: `b2b_capture_shape`, lines 739–743, 749–768 | The repeated private capture-field calculation may land now and await a later shared-file window. | The five-line local `hslot` calculation is the existing `b2b_capture_shape` calculation up to bound-variable names, and re-establishes `embedSlot_unselected` after exposing its body. Both capture-field branches repeat the same private representation dependency. This is small, disclosed duplication, not a copied host or a false theorem; nevertheless policy §1 requires **every instance** of duplicated proved material to be human-approved. The packet supplies an agent-maintainer recommendation to defer, not that acknowledgment. No approval of this new C1 copy or its scheduled resolution is identified. | Prefer adding public `embedSilentCfg_cap` in `Build/Embed`, for arbitrary frame, prefix, output, and source configuration, and replace the local `hslot` and two capture-field `change` blocks. The proposed statement is given below. If this must be deferred: **human acknowledgment required**, explicitly naming this copy and a definite shared-file landing window/owner. Add it to the debt record and reuse the export in the earlier consumer when that window occurs. |
| m1 | minor | Unit: `guessRunTM_accepts_iff` docstring, lines 633–634 | A stream whose first verdict is `rej` gives no accepting branch. | The generic theorem permits `acc = rej`; `guessRunRed` tests `acc` first. The bundled coincident-verdict sanity example correctly returns `[true]`. The formal iff uses `state = some acc`, so it is correct. | Say “a first verdict equal to `rej` **and different from `acc`** gives no accepting branch,” or express the sentence directly using the tested predicate `state = some acc`. Do not add an unnecessary distinctness assumption to the generic theorem. |
| m2 | minor | `scripts/mkprobes.py`: `neg4` and `neg1`; `scripts/runall.sh`; elaboration log and pack's negative-control description | All four substitutions make a sanity statement false; `neg4` refutes liveness at the handoff; `neg1` moves the stream two bits early. | `neg4` changes the bound from length `< 15` to `< 16`. At length **15**, the handoff theorem gives a live run-entry state, so the stronger proposition remains true. The reported error is an application type mismatch from passing the weaker hypothesis to the unchanged proof. Separately, `pre` has length 3 and `pre.take 2` length 2: `neg1` moves the stream **one** bit early. | Make handoff-time liveness a positive test. Replace `neg4` with a concrete false liveness assertion after a known halt, e.g. the accepting two-cell branch at length 19, checked with `decide`; inspect that expected failure. Relabel `neg1` as one bit early. Preserve the old log and acknowledge its description in resolutions; regenerate corrected evidence. |
| m3 | minor | `scripts/names_asm.py`, line 120; `scripts/runall.sh`, lines 245–249 and 265–267; pack's evidence attestations | Every named check fails closed, including pending-name clashes and generation of isolation evidence. | I supplied a pending file declaring `Turing.guessRunTM`: the screen reported one shared full name but returned **0**, because its exit condition ignores `hits_total`. The runner therefore records `PASS names: no clash`. I also made a syntax-equivalent parenthesization of the writer argument that makes the isolation builder's replacement assertion fail: its pipeline returned **0** and left the previous isolation file byte-identical. The runner subsequently elaborates that existing file without checking generation success. These are demonstrated failure paths, not claims that the supplied successful logs were fabricated. A smaller reporting error: the pack's short-name summary omits the `GuessRunPhase.State` overlap shown in its log. | Include pending conflicts in the name-screen exit condition, or use an explicit reviewed allowlist. Delete each generated isolation target before generation; check and aggregate the builder's own status, require a newly generated file, and run Lean only after success. Propagate producer failures through pipelines. Add controls for both failures. Until repaired, narrow the blanket fail-closed attestation; correct the short-name summary as well. |

**Rulings on the four open questions.**

1. **Keep the rewind inside the assembly and keep the new `Build.Catalog` import.** The assembly restores the stream head and charges the exact rewind cost, as ruling 2 requests. These are actual public catalog machines and framed contracts; having every caller reconstruct that step would weaken the shared interface. The proposed cut has exactly the old two imports plus `Build.Catalog`, without importing `NDHost` itself. The full-tree no-cycle/downstream claims are consistent with the provided logs; the complete import graph is not bundled. Re-run the cut and affected closure at the actual landing tip, as the pack promises.
2. **UN's setup may remain a fill obligation.** Put the probe's `hsetup` verbatim in UN's brief, including quantifier order, first exit, complete cleanup, and the absence of an input-length term in its bound. It is composition of parsing, expansion, clearing, and rewinding, not a new reusable control host. Its construction and ledger must actually be supplied in the fill; the conditional consumer probe does not prove that construction. Preserve the separate H1 harvest prerequisite.
3. **Add the public `embedSilentCfg_cap` export.** The proposed deferred timing needs the acknowledgment in M1; it is not automatically authorized by this audit. The smallest repair is to add and use the export with this landing. The export should describe both capture tape and capture head for general parameters, not just the empty instance used here.
4. **Keep the verdict leaf inline.** It is a single stationary, nonwriting transition with one emitted bit and a halt, reused through this assembly. The docstring explicitly discloses the missing exact primitive. `OracleTM.answerAction` belongs to a different action type; the existing `FinTM.emitAction` singleton route used in `Inclusions.lean` takes two steps and is not this one-step leaf. No new control architecture is hidden here. Register a standalone row if independently needed elsewhere.

The export required by ruling 3 can have the following statement, inside `Build/Embed`'s existing variable context:

```lean
theorem embedSilentCfg_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes cap =
        FinTM.bufferTape (pre ++ c.output) ∧
      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos cap =
        ((pre ++ c.output).length : ℤ) := by
  simp [embedSilentCfg, embedSlot_unselected ι cap hcap]
```

This is a repair proposal, not a separately kernel-checked addition. Its two equations follow directly from the existing private off-range equation. It avoids exporting the private search implementation.

**Definition and instance restatements.**

| Declaration | Independent reading of the body; comparison with prose and use |
|---|---|
| `NDWriterState.instFintype` | Transport finiteness from `Option Q`: `some q` corresponds to `run q`, `none` to the live control state `done`. It does not identify `done` with a halted configuration. Correct for finite consumers. |
| `GuessRunPhase` | A six-element tag type: setup, guess, forward skip, backward seek, deterministic run, and output. Its derived equality and finiteness are appropriate. The tag order itself does not impose execution order; the redirect table does. |
| `GuessRunPhase.State` | Assign respectively `SP`, `NDWriterState Unit`, `SeekPhase`, `SeekPhase`, `SQ`, and `Bool` as the phase-local control types. Correct tagged state space; all phases use the same physical tape bank. |
| The two explicit `GuessRunPhase` instances | Dispatch finiteness and decidable equality to the six component types. Finiteness of `SP` and `SQ` is required when bundling the host, not when stating raw configuration identities. Both probes supply it. |
| `guessRunPhases` | Use the deterministic lifts of `P`, the two catalog seeks, and `Q`; use the trivial-controller bounded writer on tape `j`; use an output phase whose current Boolean state is emitted before halting. The output phase ignores the external choice bit, moves no head, and writes no work cell. Its declared initial state `false` is irrelevant to redirected entries at `true` or `false`. |
| `guessRunRed` | Redirect setup exit to writer start, writer completion to forward skip, skip completion to backward seek, and backward completion to `qentry`; redirect `acc` to output `true`, otherwise `rej` to output `false`. Nothing else redirects. Acceptance wins if the two verdict states coincide. A phase's own halt propagates. |
| `guessRunTM` | Instantiate the existing `phaseHostND` with those phase machines and redirects, starting at the tagged initial state of `P`. This is a composition of the current host, not another host implementation. Only the writer's transitions depend on choices. |
| `guessRunCfg` | Force live state `q`; overwrite precisely the interval of length `s.length` beginning at the current head of tape `j`, using the bits of `s`; preserve the rest of that tape and every other field. In particular, it preserves setup output and restores no head by definition: the handoff theorem proves that the assembly actually reaches this configuration. |
| `streamStartCfg` | Force live state `q`, native input position 1, all work heads 0, empty output, `bufferTape s` on tape `j`, and blank tapes elsewhere. This is definitionally the core contract's local `start` after substituting its parameters. For empty input, position 1 is the right delimiter under the model's convention. |

The two private helpers are ordinary state-map composition and a split of a sufficiently long list into a prefix, one bit, and a suffix. I found no public equivalent with those exact statements in the supplied source subset and no wholesale copied machine/proof family. M1 identifies the separate, concrete repeated capture calculation; the one-fifth escalation threshold is not a permission to introduce smaller unacknowledged copies.

The evidence-only definitions also have their advertised meanings: `sanPStay` and `sanQStay` idle; `sanPBlock2` writes two cells and returns the head; its two-tape variant leaves capture tape 1 untouched; `sanQRead` accepts exactly the two-bit pattern `true,false`, optionally emitting on its reading steps; `sanι` selects tape 0 of two; `sanPHalt` rejects on its first transition; `sanQHaltTrue` halts with `[true]` without visiting a verdict; and `sanPBlock2Dirty` additionally writes cell −1. They are diagnostic fixtures, not production duplication.

**Writer contract and exact accounting.**

The assembly invokes `ndWriterTM_run_block` once, with precisely its gated `Unit` controller, constant transition, false stop predicate, and bounded flag `true`. Its initial writer configuration is `cP` with only the live state changed, so the original nonblank-block and blank-end hypotheses apply unchanged. The contract gives the first `m` bits of the writer segment, completion after `m + 1` steps, and the no-earlier-`done` guard; it does not require the additional left blank used later by the rewind. The isolation builder copies that current contract's statement verbatim apart from the theorem-to-axiom/name substitution; the reported dependency isolation is source-consistent, subject to the execution limitation above.

| Stage completed | Cumulative number of choices consumed |
|---|---:|
| Setup | `TP` |
| Dispatch to writer | `TP + 1` |
| Writer, including its blank-reading completion step | `TP + m + 2` |
| Dispatch to skip | `TP + m + 3` |
| Skip over the blank after the block | `TP + m + 4` |
| Dispatch to backward seek | `TP + m + 5` |
| Backward seek | `TP + 2*m + 8` |
| Dispatch to run | `TP + 2*m + 9` |
| Run to its first verdict, dispatch, and emitting halt | `TP + 2*m + TQ + 11` |

Thus the stream is exactly `(w.drop (TP + 1)).take m`. For every `s.length = m` and every `B ≥ TP + 2*m + 9`, the word

```lean
List.replicate (TP + 1) false ++ s ++
  List.replicate (B - (TP + 1 + m)) false
```

has length `B` and that stream. All other choice positions are ignored by deterministic transitions, dispatches, or the writer's completion step.

Writing the setup's stream-head position as `cP.workTapePos j`, the writer, skip, and backward seek move it successively to

\[
cP.workTapePos\ j+m,\qquad
cP.workTapePos\ j+m+1,\qquad
cP.workTapePos\ j+m+1-m-1=cP.workTapePos\ j.
\]

The other heads never move during these phases. The seeks write nothing; the writer preserves every cell outside its interval. The backward seek may visit the blank one cell left of the block, which is why `hleft` is a real hypothesis.

**Assessment of all eight theorems and their hypotheses.**

| Theorem | Truth and consumer adequacy |
|---|---|
| `guessRunTM_runWith_handoff` | Correct modulo the gated writer contract. The four phase guards stop the host from dispatching early. The writer supplies the delimited word required by the two public seek contracts; the table above accounts for every step. It preserves arbitrary setup data outside the written block, which D needs. |
| `guessRunTM_runWith_live` | Correct: pad a shorter word to the handoff length; an earlier halt would be absorbing and contradict the live configuration at handoff. Liveness also holds at the handoff itself by the handoff equality; the strict bound is sufficient, but not sharp. |
| `guessRunTM_runWith` | Correct. Before the first verdict, both run-phase slices coincide with `Q`; then one dispatch and one leaf step append the predicate `decide (d.state = some acc)` and halt. Longer words are absorbed. The resulting output includes any setup/run emissions, exactly as the statement says. |
| `guessRunTM_runWith_setup_halt` | Correct and independent of the writer contract. Before any exit visit the host is the tagged deterministic setup; if that setup halts, all later choices are absorbed. `TP` need not be the first halting time. This is appropriate for D's early rejection provided its setup output is nonaccepting. Halting alone does not imply rejection. |
| `guessRunTM_haltsWithin` | Correct. Extract the stream from each word of the uniform total length and apply the whole-branch theorem at its bounded first verdict time. This gives all-branch termination, not merely an accepting branch. |
| `guessRunTM_accepts_iff` | Correct in both directions. Forward, `d.output ++ [verdict] = [true]` forces `d.output = []` and the verdict predicate true. Backward, the first-verdict witness on the right equals the bounded witness supplied by `hQ`: either strict inequality would contradict one witness's no-earlier-verdict clause. Hence the apparently unbounded existential time is ≤ `T`; pad a realizing word to `B` and apply the branch theorem. Only m1 affects the prose. |
| `guessRunCfg_clean` | Correct. Overwriting the full stream interval removes any dependence on the old interior values; blankness outside makes its final tape exactly `bufferTape s`. Selected nonstream tapes are blank; the capture tape and all frame tapes are blank with heads 0; input/state/output also agree. It correctly needs only outside blankness, not interior nonblankness, because this theorem is a pure configuration identity. M1 concerns reuse of proof material, not its statement. |
| `guessRunTM_silent_spec` | Correct. Exact support of `blk` supplies the writer and delimiter hypotheses, while the clean identity supplies the silent embedding's initial configuration. Its lockstep theorem preserves core states and fixes physical output to `[]`; the verdict leaf supplies the sole physical emission. No restriction on the core's own output is missing. This is the interface UN needs. |

The setup and suffix first-exit hypotheses are necessary to identify the host's actual dispatch times. Separate no-earlier-halt assumptions would be redundant: a deterministic run that reaches a live exit cannot have halted earlier. `hblock` and `hend` fix the writer's stopping position; a hole stops it too soon and an absent right delimiter can extend writing. `hleft` fixes the rewind position. All are satisfied by the clean setup, and none imposes a spurious condition on the consumers.

The universal `hQ`/`hR` verdict hypothesis is deliberately stronger than “some stream accepts”: every branch must terminate for the complexity-class conclusion, and a run that halts on its own with `[true]` would otherwise bypass the verdict characterization. Uniform bounds suffice for both consumers; no per-stream-budget iff is needed for this gate. The raw interfaces need no finiteness beyond the instances used when constructing `FinNDTM`.

**Core and consumer sufficiency.**

For the core, the silent embedding places each source tape at its selected host tape. At every simulated time its capture tape contains the core's accumulated emissions, with its head at their length; its physical output remains empty. In particular, silence does not mean erasing information that the core reads: the source model cannot read its write-only output, and the extra capture tape lies outside the source selection. State and native-input trajectories remain exact. The final leaf emits `true` precisely when the first verdict is `acc`, including the specified precedence when verdicts coincide.

**UN.** Removing whitespace, the conclusion of `probe_universal_of_setup` is identical to the frozen `exists_timed_universal_NDTM` statement. The machine is chosen before `α`, `x`, and `t`; only the constant depends on the code. The setup hypothesis likewise chooses one finite `P` before these inputs. For each code the calculation is

\[
\begin{aligned}
TP+2t+C_R(t+1)+11
&\le C_P(t+1)+C_R(t+1)+2t+11\\
&\le (C_P+C_R+13)(t+1),
\end{aligned}
\]

because `13(t + 1) − (2t + 11) = 11t + 2 ≥ 0`. With `s.length = t`, `s.take t = s`, so the core's accepting-verdict predicate becomes exactly the coded machine's `AcceptsWithin x t`. The core's distinct verdict states rule out interpreting its reject branch as acceptance. Its first-verdict clause makes the converse witness unique. The prefix clause is preserved in the supplied core contract, though UN needs only its total bound.

`hsetup` is a credible, nonvacuous **remaining construction obligation**, not a proved consequence of the probe. Extract the binary budget from the nested initial header, expand it to a contiguous `t`-cell block, clear the counter/scratch bank, rewind the stream, and restore the input head. Expansion with a singleton pattern has cost at most `2t + 4t + 2*(Nat.bits t).length + 2` by the supplied expansion and counter-overhead contracts; cleanup and rewinds are linear in the same lengths. This fits `O(t + 1)` without scanning `x`. The exact prefix parser and its composition ledger must be demonstrated in the fill; foundational parser/encoding modules are not all bundled here. `k` is existential and may provide scratch tapes; no fixed inadequate bank is imposed. No conclusion here treats that inference as an already machine-checked setup.

**D.** Probe 2 bundles the same fixed finite machine and proves membership of its stream-characterized language in `NTIME (fun n => g n + 1)` using the stated constant `A`. Its time inequality includes setup, writing, rewind, dispatch, run, and final output; setup output is correctly included in the required empty-output test. It does not prove the actual locator, top-rung flip, timeout routing, or identification of that language with D's intended language: those are precisely the disclosed fill obligations. The probe assumes every input reaches the guessing exit. To use early setup halts on malformed inputs, combine the separate setup-halt theorem with the appropriate rejection/time argument; alternatively choose the disclosed empty-block/rejecting-suffix route, which fits this probe directly. There is no missing assembly architecture in either choice.

**Adversarial instances required by brief point 11.** These are mathematical boundary checks; the finite executable checks cited below use a separate Python transcription of the transition bodies, not Lean elaboration.

| Case | Result |
|---|---|
| (a) `m = TP = TQ = 0`, setup already at exit, immediate acceptance | Handoff at 9, live output state at 10, halted with `[true]` at 11. Independently checked all 2,048 length-11 words. |
| (b) Immediate rejection | The same schedule emits `[false]` at 11. |
| (c) `acc = rej` | Emits `[true]`, by acceptance-first dispatch. This is permitted and exposes m1. |
| (d) Two-cell block | For `sanPBlock2`, `TP = 2`, handoff is 15. Independently checked all 32,768 length-15 words: every prefix remains live, and at 15 the state is the run entry with head 0. This also disproves the intended interpretation of `neg4`. |
| (e) Empty choice word | Leaves the initial tagged setup configuration unchanged and live. |
| (f) Longer than halting time | A length-40 word with the accepting two-bit stream has the same halted output; absorption applies to arbitrary extensions. |
| (g) Wrong stream positions | The two-cell setup uses zero-based indices 3 and 4. Moving `true,false` one position left can change acceptance to rejection. Prefix/dispatch bits do not substitute for writer bits. |
| (h) Noisy core | The accepting two-step reader directly produces `[true,true,true]`; silent embedding produces host output `[true]`, capture contents `[true,true]`, and capture head 2. |
| (i) Halt with `[true]` but no verdict | Starting after an empty guess, this suffix halts the host at 10 with `[true]`, although no first accepting verdict exists. It violates `hQ`; removing that hypothesis makes the general iff false. |
| (j) Dirty cell immediately left of block | The supplied dirty setup makes the rewind start the suffix at cell −1. The stream `false,true`, rejected after clean setup, is then accepted by the same reader. `hleft` cannot simply be dropped. |
| (k) Setup halts immediately | “Immediately” is the first transition, time 1, not time 0. The host retains `[false]` for all later words and never guesses. A halted initial configuration is impossible here. |
| (l) Onto selection | If `ι` is onto, `cap ∈ Set.range ι`, contradicting `hcap`; this deliberately excludes overlap. Inclusion into `K + 1` tapes with the last tape reserved is nonvacuous. Likewise `j : Fin 0` is impossible; the core supplies a stream tape and therefore has positive tape count. |
| (m) Earlier visit to `pexit` | Let setup alternate two states, starting at `pexit`, and return at time 2 with an empty block. Ignoring `hPfirst` and reporting `TP = 2` predicts handoff at 11, but the host dispatched at 0 and is already halted at 11 with an immediately accepting suffix. The first-visit hypothesis is essential. |

Useful permanent additions are a positive handoff-time liveness corollary (directly from the handoff equality), the corrected false post-halt liveness control, and an early-setup-exit example. These strengthen evidence around actual boundary risks; they do not replace the quantified theorems.

**Decisions, home, attribution, and evidence ledger.**

The active route is respected: one guess-first phase, no nondeterministic round loop; `BF := E(UN)` remains in `ExhaustiveReplay`; the core still interprets replay machines at three work tapes; the shared step clock remains a consumer dependency rather than a new assembly clock; and UN's core retains window-copy/input-locality routing. The original C1 design's three-stage sketch is openly refined to six phases to account for rewind, live verdicts, and emission capture. Ruling 2's requirements are all covered by the eight statements. The historical design's “proposed, not drafted” status is explicitly superseded by this pack.

`Build/NDHost` is the home required by ruling 2. Raw `NDTM` acceptance is appropriate construction-layer plumbing: importing `ClassNP` merely to write the bundled acceptance abbreviation would reverse the intended layering. The supplied consumer probes perform the finite bundling at that layer. The unit's public declarations have statement prose, the nontrivial proofs have literal proof-sketch paragraphs, and the leaf's construction is disclosed. The recorded file-size exception permits this coherent 1,064-line module; it does not waive M1.

I independently consulted the [2009 book, printed pp. 41–42 and 64](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf). Section 2.1.2 and the proof of Theorem 2.6 support the guess-then-verify construction and all-branch time convention; Exercise 2.6(b) is the linear-overhead universal-NDTM exercise. The exact timing constants, tagged live exits, and capture interface are library-specific refinements, not literal textbook statements. No attribution repair is needed for those references.

| Evidence claim | Independent result and limits |
|---|---|
| Bundle identity | Digest and 53-section count verified. Original upload left unchanged. |
| Unit identity | 896 lines; SHA-256 `de3534f77d46dc1880423b9eec001bab4a801aee4c8c6d51efa46fdb165d9649`, matching the elaboration log. Twenty explicit declarations: 18 public, two private. No admission or forbidden execution construct found in the new executable code. |
| Probe/cut/landing reproduction | Regenerated sanity, axiom, consumer, cut, and landing files with the supplied builders; all five are byte-identical to the supplied artifacts. The part is 849 lines, cut 1,046, and landing 1,064. |
| Freeze | Supplied check passes: code lines 90 + one import + 622 = 713; existing six declarations remain first and in order; the 137-line tail is verbatim. A separate nested-comment/string-aware comparison independently agrees. Only the documented import, module prose, and appended part change. |
| Consumer statement fidelity | Independently compared UN's consequent with the frozen theorem after whitespace removal: identical. The probe does not import `NTimeHierarchy` or cite the theorem it derives. |
| Isolation | Regenerated both isolation files: one writer substitution in each, and one core substitution only in the universal probe. Copied contract signatures agree with the bundled sources. Reported axiom sets distinguish the six writer-dependent results from the two writer-independent results; these axiom prints were not independently rerun. m3 limits automated freshness guarantees. |
| Sanity evidence | Sixteen supplied examples and the three genuinely false controls have source-consistent meanings. `neg4` is m2. Independent transition experiments cover the boundary table above. |
| Width and lint | Re-ran the supplied checks: zero over-100-character lines; 0 FAIL and 1 file-size WARN. The unit's longest line has 98 characters. Mechanical lint is not a waiver of semantic prose or reuse policy. |
| Name screening | Against the 19 bundled TCSlib sources, the script screens 907 names and finds no full-name clash; its two existing-name controls are detected. The 716-file/16,926-name/298-pending-unit census needs the unavailable full tree. A pending-only collision returns success, as m3 records. The small short-name summary omission is also included in m3. |
| Cited identifiers | Reproduced the 78-token lexical population. The log's 41 unresolved tokens are compatible with its listed variables, modules, constructors, and local `start`; I did not rerun their Lean resolution. |
| Base, snapshots, pending PRs, and process history | Supplied logs identify `e831b5b0d887dac3bbf1aa2c19af28983b15b982` and the stated snapshot. The bundle cannot independently establish the full commit tree, snapshot equality, all pending-PR contents, global import graph, or historical no-write claims. `BUNDLE-FILES.txt`, wrapper, full dependency tree, and snapshot are absent. These are verification limits, not evidence of an altered statement. |

To close this gate, resolve M1 through the shared export or the specified human debt acknowledgment, and record the disposition of m1–m3. Then perform the declared landing-tip replay and registry/plan/backlog updates. The assembly's statements themselves do not need relaxation.

**Glossary.** The notation used is inherited from the packet; the following records its meaning here.

| Notation | Meaning |
|---|---|
| `P`, `pexit`, `TP`, `cP` | Deterministic setup, its live exit, reported first-exit time, and exit configuration. |
| `Q`, `qentry`, `acc`, `rej`, `TQ`, `d` | Deterministic suffix, entry/verdict states, first-verdict time, and configuration at that time. |
| `R`, `entry`, `TR`; `UN`, `D`, `E`, `BF` | Interpreter core and its entry/time; universal NDTM, diagonalizer, exhaustive decider, and `E(UN)`. |
| `m`, `s`, `w`, `T`, `B` | Stream length, stream, complete choice word, uniform suffix bound, and total choice budget. |
| `k`, `K`, `j`, `jR`, `ι`, `cap`, `blk` | Host/core tape counts, stream tapes, tape selection, capture tape, and setup block. |
| `SP`, `SQ`, `SR`, `S`, `Symbol` | Setup/suffix/core or general state types, and tape-symbol type. |
| `z`, `x`, `α`, `c`, `t`, `C_P`, `C_R`, `g`, `A` | Native input, simulated input, code, code scheme or source configuration according to context, simulated budget, setup/core constants, target time function, and membership constant. |
| `pre`, `out₀`, `tapes`, `heads` | Capture prefix, fixed physical output, and ambient tape/head frame in the proposed export. |
| `O(t + 1)`; live; absorption | Constant-factor linear bound; a configuration with state `some q`; invariance under further steps after state becomes `none`. |
