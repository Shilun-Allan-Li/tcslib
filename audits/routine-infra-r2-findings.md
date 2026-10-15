# Machine-routine layer (§12), round 2: repair audit

**Verdict: FAIL — 1 blocker, 0 majors, 0 minors, 1 note.** The gate remains open. Both new returning-run contracts are false for an initially halted configuration at time zero. The positive-time returning construction works; the seven other new contracts are sound as stated. Round-1 R2–R10 are disposed of at this statement gate; R1 remains open because of the new counterexample.

Audited packet: `routine-infra-r2-bundle.md`, reported commit `9a92fa1aeb377d568972e42229979cf81562ba41`, branch `complexity/arora-barak-ch3-4`. Audit date: 2026-10-09 UTC. Independently computed SHA-256 matches the supplied value:

```text
fc7afcb8a469914c4b6a672348769329cfe708c013c64cfbb957481aadb2a3cf
```

Scope: the complete supplied repair diff, three new definitions, nine new sorried contracts, repaired sketches and scope statements, and design §12.5. References below use **extracted attachment line numbers**, not bundle line numbers. This is a statement audit: the mathematical arguments below are not kernel-checked Lean proofs. No source changes were made.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | blocker | `Build/Embed.lean:489–508,523–540` · `embedSilentRetTM_run`, `embedEmitRetTM_run` | The stated first-halt hypotheses do not ensure a live initial configuration, but the conclusion always requires a live return anchor. | Choose `T = 0` and `c.state = none`. The live-prefix hypothesis is vacuous; `hhalt` holds. `Cfg.mapState Sum.inl` preserves `none`, and `runFrom … 0` is the initial configuration. Thus the left side of the handover equality has state `none`, while the right side explicitly has state `some (Sum.inr ())`. Projecting the claimed equality onto `.state` contradicts constructor disjointness. This refutes both contracts, independently of any tape behavior. | Add `hT : 0 < T` or `hc : c.state ≠ none` to both contracts. Under the existing hypotheses these are equivalent remedies, and the positive-time proof below applies. If zero-time returns are required, change the initial configuration transport to send source `none` to the live return anchor, as `captureCfg` does; ordinary `Cfg.mapState` cannot do that. |
| R2-2 | note | Round-2 pack · Brief item 1 | The total inventory is correct, but its run/space subdivision is misstated. | The nine new contracts comprise **five run/first-return contracts and four visited-set contracts**, not six and three. The fourth visited-set contract is `seamReleaseTM_visitedByTapeHead`. All nine were audited. | Correct the inventory sentence. No Lean statement change is needed. |

R2-1 is one shared defect affecting two declarations. Its blocker classification follows the pack's definition: downstream work would import a false statement, not merely an incomplete sketch.

## Counterexample, with every hypothesis checked

Use `m = 0`, `k = 1`, `S = Unit`, input `[]`, the unique injection `ι : Fin 0 ↪ Fin 1`, and `cap = 0`. Let `M` have initial state `()` and a transition that emits `true` and halts, with stationary input motion. Take

```lean
c := { M.initCfg [] with state := none }
T := 0
```

Set the frame tapes blank, frame heads zero, and all prefixes empty. These choices are legitimate: the contracts accept an **arbitrary configuration** `c`, not only `M.initCfg x`. For the suppressing contract, `Set.range ι = ∅`, hence `hcap` holds.

The two time hypotheses reduce to

\[
\begin{aligned}
&\forall t\in\mathbb N,\ t<0\Longrightarrow
   (M.\mathrm{runFrom}\ c\ t).\mathrm{state}\ne\mathrm{none},
   &&\text{true because no such }t\text{ exists},\\
&(M.\mathrm{runFrom}\ c\ 0).\mathrm{state}
   =c.\mathrm{state}=\mathrm{none},
   &&\text{true by the definition of iteration.}
\end{aligned}
\]

Let `d` be the transported configuration `embedSilentCfg ι cap tapes heads pre out₀ c`. From the definition, `d.state = none`, and `M.runFrom c 0 = c`. The middle conjunct of `embedSilentRetTM_run` therefore asserts an equality whose state projection is

\[
\begin{aligned}
&\bigl((\mathrm{embedSilentRetTM}\ \iota\ \mathrm{cap}\ M).
  \mathrm{runFrom}\ (d.\mathrm{mapState}\ \mathrm{Sum.inl})\ 0\bigr).
  \mathrm{state}\\
&\qquad=(d.\mathrm{mapState}\ \mathrm{Sum.inl}).\mathrm{state}
       =\mathrm{Option.map}\ \mathrm{Sum.inl}\ \mathrm{none}
       =\mathrm{none},\\
&\{d\ \mathrm{with}\ \mathrm{state}:=\mathrm{some}(\mathrm{Sum.inr}())\}.
  \mathrm{state}=\mathrm{some}(\mathrm{Sum.inr}()).
\end{aligned}
\]

Consequently the asserted equality implies

\[
\mathrm{none}=\mathrm{some}(\mathrm{Sum.inr}()),
\]

which is false. Replacing the suppressing transport and machine with their forwarding versions gives the identical contradiction for `embedEmitRetTM_run`.

The source's actual transition is never executed in this counterexample. Changing the returning machines' transition tables alone cannot repair a zero-step equality.

## Definition restatements and nine-contract coverage

The following restatements follow the definition bodies and theorem types. `Cfg.mapState f` maps the optional control state and preserves all other fields; in particular, it maps `none` to `none`. Visited sets include positions at **all times from zero through the stated horizon**, inclusive.

| New definition | Meaning from the body | Comparison with the intended interface |
|---|---|---|
| `embedSilentRetTM` (`Embed:441`) | States are `S ⊕ Unit`, starting at `Sum.inl M.q₀`. In a left state, execute the suppressing embedding core, then replace a live successor by its left image and a halting successor by the live right anchor. At the right anchor, take a stationary, silent, write-free self-loop. | Correct halt-to-live action transformation. Capture requires the capture tape to be outside the selected bank, as the run contract correctly requires. The definition does **not** revive an already halted starting configuration. |
| `embedEmitRetTM` (`Embed:457`) | The same successor transformation and idle anchor, using the forwarding core instead. | Correct: the optional final emission is appended before the successor becomes the live anchor. An already halted starting configuration still remains halted. |
| `seamReleaseTM` (`Seam:399`) | States are `Unit ⊕ S`, starting at the fresh left state. Its action is exactly `M`'s action at `anchor`, with successor mapped into the right copy. Right states simulate `M` with the same mapping; a source halt remains a halt. | Correct execute-first adapter. It adds **no extra source-simulation step**: the first source action executes on its first transition. The later seam dispatch adds its separate one step. |

| New contract | Exact content and assessment |
|---|---|
| `embedSilentRetTM_run` (`Embed:489`) | Assuming the source is live before `T` and halted at `T`, assert full transported configuration equality at every earlier time, equality at `T` after replacing control by the live return anchor, and no earlier visit to that anchor. **False at `T = 0`**, as above. For positive `T`, induction transports every live step; the final action performs all input, work-tape, and capture effects before its successor is replaced. |
| `embedEmitRetTM_run` (`Embed:523`) | The same three conclusions, with physical output `pre ++ (M.runFrom c T).output` at handover. **False at `T = 0`**. For positive `T`, the same induction preserves tape effects and appends the last emission before entering the anchor. |
| `embedSilentRetTM_visitedByTapeHead` (`Embed:552`) | For arbitrary `c`, horizon, and tape, the returning and closed suppressing machines have equal visited sets from their respective initial configurations. **True without `hcap`.** Compare the two host machines directly: their live actions have identical non-control effects, and after a halt their respective halted state and return anchor are both stationary; if initially halted, both remain halted. This proof does not require the false run contract or source/capture separation. |
| `embedEmitRetTM_visitedByTapeHead` (`Embed:570`) | The same all-time, per-tape equality for forwarding. **True.** The identical-action comparison holds before the source successor becomes `none`; afterwards the closed machine is absorbed and the returning machine idles. It also covers runs that never halt. |
| `seamCompTM_run_ofCfg` (`Seam:329`) | Given an exact first arrival of phase one at live `exit`, and an exact phase-two run starting from `c₁.mapState (fun _ => entry)`, conclude full composite configuration equality at `T₁ + 1 + T₂`. **True.** The first-return cut permits left lockstep through `T₁`; the stationary dispatch changes only control; right lockstep then runs for `T₂` steps. The endpoint `c₃` may be halted. |
| `seamCompTM_firstReturn_ofCfg` (`Seam:349`) | Add a live final state `q₂` and its phase-two cut, and conclude that the composite never visits `Sum.inr q₂` before `T₁ + 1 + T₂`. **True.** Through time `T₁`, the composite is in the left copy; at later times the right injection transports the phase-two cut. The endpoint equality comes from the separate run theorem; this theorem's conclusion itself is the exclusion clause. |
| `seamCompTM_visitedByTapeHead_ofCfg` (`Seam:374`) | Under phase one's endpoint and cut hypotheses, the composite's visited set through `T₁ + 1 + T₂` is contained in the union of phase one's set through `T₁` and phase two's set through `T₂`, from the actual returned configuration with relabelled control. **True.** There is no phase-two endpoint hypothesis, and none is needed. Both trajectory segments are exact; dispatch repeats their shared endpoint/start head positions. |
| `seamReleaseTM_firstReturn` (`Seam:425`) | Given a live initial anchor, positive `T`, an exact live return to that same anchor, and exclusion only at strictly positive interior times, conclude exact endpoint transport and exclusion of `Sum.inr anchor` at **all** earlier adapter times, including zero. **True.** The fresh step executes the anchor action; at every positive time, the adapter is the right-mapped source run. At time zero the fresh left state is distinct from the right return anchor. |
| `seamReleaseTM_visitedByTapeHead` (`Seam:446`) | Starting from any live anchor configuration, the release adapter and source have equal visited sets on every tape at every horizon; neither a return nor termination is assumed. **True.** Heads initially agree, and positive-time runs agree after right state mapping. If the source halts, both versions halt; if it runs forever, the same induction applies at every finite horizon. |

For the corrected returning-run contracts, the induction has an essential last-step case: `T > 0` gives a predecessor time `T−1`, whose source state is live by `hlive`. The shared core applies the entire action there, including the final write, head movement, and emission; only its optional successor changes. Before that step, states lie in `Sum.inl`, so constructor disjointness proves the first-visit clause. This establishes the proposed positive-time repair mathematically; it is not a claim that the repaired Lean proofs have been filled.

The capture-specialization tape-count correction is accurate: use `ι i = i.castSucc` and `cap = Fin.last m` in an `m+1`-tape host. At a **live** source configuration, ordinary state mapping reproduces the corresponding `captureCfg` state. At a halted source configuration, the returning `captureCfg` instead uses `some ((c.state.map emb).getD ret)`; that extra halt-to-live replacement is essential, not an ordinary `Cfg.mapState` operation.

## S7, S8, and S9 replay

**S7 — two-step write and self-return.** Use one work tape, states `q,r`, and stationary input/work heads. State `q` writes `true` at cell zero and enters `r`; state `r` makes no write and enters `q`. Start with a blank tape, empty output, and control `q`. The source run has states `q,r,q` at times `0,1,2`, and its returned word is `[true]`.

| Time | Release-adapter state | Tape word | State when used as the left phase of a seam composite |
|---:|---|---|---|
| 0 | `Sum.inl ()` | `[]` | `Sum.inl (Sum.inl ())` |
| 1 | `Sum.inr r` | `[true]` | `Sum.inl (Sum.inr r)` |
| 2 | `Sum.inr q` | `[true]` | `Sum.inl (Sum.inr q)` |
| 3 | Adapter alone would execute `q` again | — | `Sum.inr entry`, tape still `[true]` |

Apply `seamReleaseTM_firstReturn` with `T = 2`: the only strictly positive interior time is 1, whose source state is `r ≠ q`. Its two conclusions supply phase one's endpoint and full cut for `seamCompTM_run_ofCfg`, with left exit `Sum.inr q`. Thus both source actions precede dispatch, whose exact cost is one. Every head in this example stays at zero, so all phase and composite visited sets are `{0}`.

**S8 — final halting emission.** Use the one-state, zero-work-tape source that emits `true` and halts on its first transition. Start it live with empty source output. Embed silently into a capture tape with `pre = [false]` and `out₀ = [true]`.

| Time | Returning control | Capture word | Capture head | Physical output |
|---:|---|---|---:|---|
| 0 | `Sum.inl ()` | `[false]` | 1 | `[true]` |
| 1 | `Sum.inr ()` | `[false,true]` | 2 | `[true]` |

At time 1 the closed embedding instead has `state = none`, with the **same** tape and output data. Both head trajectories subsequently stay at 2, giving capture visited set `{1,2}` for every horizon at least 1. The returning anchor is absent at time zero, so the `T = 1` instance of the intended contract succeeds. Used as a seam's left operand, its controls are `Sum.inl (Sum.inl ())`, then `Sum.inl (Sum.inr ())`, then `Sum.inr entry` at time 2; dispatch preserves the captured word.

For the forwarding flavor, take physical prefix `[false]`. The same action yields output `[false,true]` at the live anchor. To test residue as well, add a selected source work tape whose final action writes `true` at its head at 2 and moves left: at handover that host tape retains the write at 2 and head at 1. An unselected frame tape with head 7 remains unchanged. These are real positive-time repairs of round-1 R1; the zero-time counterexample remains separate.

**S9 — arbitrary frame and output-carrying seam.** Take two tapes and input `[true,false]`. Start at input position 0, work heads `(0,7)`, and output `[true]`. The frame tape may contain noncontiguous data, for example `false` at 7 and `true` at 100. Phase one, in one step, writes `true` on tape zero, moves that head right, emits `true`, attempts a left input move, and enters `exit`. Phase two, in one step, writes `false` on tape zero, moves that head left, emits `false`, moves the input head right, and enters `done`.

| Composite time | Control | Input position | Work heads | Output |
|---:|---|---:|---|---|
| 0 | `Sum.inl start` | 0 | `(0,7)` | `[true]` |
| 1 | `Sum.inl exit` | 0 | `(1,7)` | `[true,true]` |
| 2 | `Sum.inr entry` | 0 | `(1,7)` | `[true,true]` |
| 3 | `Sum.inr done` | 1 | `(0,7)` | `[true,true,false]` |

The frame tape's **whole contents** are identical at every time. The dispatch from time 1 to 2 changes only control, so `seamCompTM_run_ofCfg` applies with `T₁ = T₂ = 1`. The composite visited sets are `{0,1}` and `{7}`, exactly the unions in the new visited-set contract. The initial input position, displaced frame head, noncanonical frame contents, and nonempty output would all have prevented a canonical `Cfg.ofWords` instantiation.

## General seam derivation and state plumbing

Under the general seam hypotheses, induction gives the following two full-configuration identities:

\[
\begin{aligned}
&(\mathrm{seamCompTM}\ M_1\ \mathrm{exit}\ M_2\ \mathrm{entry}).
 \mathrm{runFrom}\ (c_0.\mathrm{mapState}\ \mathrm{Sum.inl})\ t\\
&\qquad=(M_1.\mathrm{runFrom}\ c_0\ t).\mathrm{mapState}\ \mathrm{Sum.inl}
 &&(0\le t\le T_1),\\[2pt]
&(\mathrm{seamCompTM}\ M_1\ \mathrm{exit}\ M_2\ \mathrm{entry}).
 \mathrm{runFrom}\ (c_0.\mathrm{mapState}\ \mathrm{Sum.inl})\ (T_1+1+t)\\
&\qquad=\bigl(M_2.\mathrm{runFrom}\
 (c_1.\mathrm{mapState}(\mathrm{fun}\ \_\Rightarrow\mathrm{entry}))\ t\bigr).
 \mathrm{mapState}\ \mathrm{Sum.inr}
 &&(t\ge0).
\end{aligned}
\]

The intervening transition has zero head movements, no writes, and no output. Since `c₁.state = some exit`, constant state mapping really does produce `some entry`; it is not an attempt to revive `none`. Splitting the inclusive time interval into `0,…,T₁` and `T₁+1,…,T₁+1+T₂` proves visited-set **equality** with the union, hence the advertised containment. Projection onto states proves the inherited cut.

The canonical instances follow by substituting

```lean
c₀ := Cfg.ofWords start w₀
c₁ := Cfg.ofWords exit w₁
c₃ := Cfg.ofWords q₂ w₂
```

and using the definitional identity

```lean
(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w
```

Thus all three canonical contracts are genuine specializations. Taking cardinalities and then summing recovers the canonical additive space bounds. For the canonical maximum bound, the idle singleton `{0}` is contained in the other phase's visited set. On a general seam, the analogous idle singleton uses the actual seam head position.

For release, the fresh state is in `Unit ⊕ S`, whereas the returning embeddings use `S ⊕ Unit`. These sums serve different purposes and are wired correctly. A released left phase exits at `Sum.inr anchor`; a returning embedded left phase exits at `Sum.inr ()`; **both** are enclosed in the composite's outer `Sum.inl` until dispatch. A positive self-return used as the right phase can likewise be released: choose its fresh `Sum.inl ()` as the seam entry and its `Sum.inr anchor` as the final anchor. The constant-map compositions preserve every data field, and the right phase's fresh constructor removes the zero-time cut obstruction.

## Round-1 dispositions and sketch checks

| Finding | Round-2 disposition | Verification |
|---|---|---|
| R1 | **Open: new blocker R2-1.** | S8 and the positive-time through-halt argument succeed, including final emissions and residue. The unqualified run statements additionally assert a false zero-time handover. |
| R2 | Closed at statement level. | The three general-configuration theorems preserve actual returned tapes, heads, input position, and output; S9 and the canonical substitutions above establish the required coverage. |
| R3 | Closed at statement level. | The release definition executes the entry action unconditionally. Its endpoint and full cut compose directly with the general seam theorem; its visited-set equality supplies the corresponding space result. S7 succeeds. |
| R4 | Closed at statement level. | The sketch explicitly commissions a **new forwarding controller**, disclaims the old captured-payload witness, and names validation/buffering, payload forwarding, and the seam. The coefficient-one space argument below is valid. This accepts a construction obligation, not a completed implementation. |
| R5 | Closed. | `C = 0` gives the fixed output `Nat.bits 0`; `e = 0` gives `Nat.bits C`. A finite-state constant-output machine uses zero work tapes. In the remaining case, `C ≥ 1`, `e ≥ 1`, so `n+1 ≤ (n+1)^e ≤ C(n+1)^e`; the unary banks, intermediate buffer, and logarithmic counter fit the stated value-linear bound. |
| R6 | Closed. | At first mismatch/word-end position `d`, the count is `d + 1 + d + 1 = 2d+2`, and the full visited interval is `[-1,d]`, with `d+2 ≤ min(\|w fst\|,\|w snd\|)+2` cells. Equal words, either proper-prefix orientation, empty words, and aliased indices are included. For aliasing, the disjunction selects one action per physical tape. |
| R7 | Closed. | A successful increment at first `false` position `p` uses `p` carries, one write/left-turn, `p` rewinds, and one right-entry: `2p+2 ≤ 2\|w i\|`. It visits exactly `[-1,p]`, never `p+1`; `[false]` takes two steps. The unchanged public bound retains legitimate slack. |
| R8 | Addressed. | The revised description correctly treats the quadratic time clause as slack and accounts for both guard and raw-strip storage. It no longer attributes the cost to replays. |
| R9 | Addressed. | The opening explicitly limits `ι` to whole distinct physical tapes with coordinates and native input unchanged. Zone multiplexing, tape-count reduction, and virtual-input interpretation are separate consumer work. |
| R10 | Addressed. | The added scope paragraph explicitly limits the exported space theorem to the decision loop. Configuration- and result-bearing same-witness space contracts remain future work, not available consequences of this declaration. |

For **R4**, let `n = |z|` and suppose `pairDecode z = some (a,b)`. The proposed host first validates/buffers with no output on invalid input, then emits the encoded first component and delimiter, then simulates `Mg` on buffered `b`, forwarding its emissions. The virtual-input controller needs a fixed number of microsteps per source step to preserve both input boundary clamps, including empty `b`; this is a construction obligation of the new controller, not something supplied by physical-tape embedding alone.

The payload work bank starts blank with heads at zero; administrative stages leave those heads stationary. During simulation its head positions are exactly source positions, possibly repeated during controller microsteps. After payload halt, the host freezes those heads. Hence the payload bank's contribution is at most `Sg |b|`, with coefficient **one**, at every horizon. For fixed implementation constants `A,B`,

\[
\begin{aligned}
\mathrm{space}_{\rm host}
 &\le Sg(|b|)+A(n+1)
 \le Sg(n)+A(n+1),\\
\mathrm{time}_{\rm host}
 &\le B(n+1+Tg(|b|))
 \le B(n+1+Tg(n)).
\end{aligned}
\]

Choose the theorem's single `c ≥ max(A,B)`. Invalid encodings halt after validation with empty output and the same administrative bounds. Forwarded output never occupies a work tape, so the unary-square payload from S11 no longer forces quadratic administration. No inherited time clause or hypothesis was weakened to obtain this repair.

## Additional adversarial checks

| Instantiation | Result |
|---|---|
| Returning run starts halted, `T = 0` | Refutes both through-halt statements; the visited-set equalities still hold. |
| Source emits nothing on its final halting action | The returning anchor is reached after the action, with capture head/output unchanged. There is no dependence on an actual emission. |
| Capture tape lies in the selected bank | Correctly excluded by the suppressing run theorem. The suppressing visited-set comparison remains true because both host variants use the same core, including the same tape-selection precedence. |
| Returning source never halts | No run-contract instance exists, but both all-time visited equalities remain valid by direct induction. |
| Both seam durations are zero | Exactly one dispatch occurs. All fields except control are preserved; each tape's visited set is its initial-head singleton, and total space is zero when there are no tapes. |
| Phase two halts early or ends halted | The general run and visited-set statements still apply. Absorption preserves right-phase correspondence. A live final-anchor hypothesis correctly excludes such an execution from the first-return contract. |
| Release returns in one step | A self-loop at the source anchor becomes fresh-left → right-anchor; the positive interior cut is vacuous and the adapter's zero-time cut holds. No additional setup step is needed. |
| Release source halts on its first step, or never returns | Its first-return theorem is inapplicable, but its unconditional visited-set equality remains sound. |
| Nonempty initial source output and host prefix | The transports retain `pre ++ c.output`; subsequent emissions append once. Silent mode also preserves the independent physical-output prefix `out₀`. |

An independent Python evaluator of the supplied transition definitions checked S7/S8/S9, capture and forwarding with nonempty prefixes, selected-tape residue and displaced frames, zero-duration seams, halted right endpoints, the zero-time counterexample, capture-bank collision for the space-only comparison, and release behavior after halt or without return. These finite checks supplement the symbolic arguments; they do not establish universal Lean theorems.

## Integrity and evidence limits

| Check | Independently established result |
|---|---|
| Bundle hash | Exact SHA-256 match shown above. |
| Repair diff | Reverse-applied every hunk exactly against the attached post-repair files, without offsets or fuzz. For all four changed files, reconstructed old and supplied new Git blob hashes match the diff's respective `index` prefixes. |
| Pre-existing theorem freeze | All **47/47** pre-existing theorem declarations, including their `by sorry` bodies, are byte-identical to the reconstructed pre-repair declarations: Embed 9, Seam 6, Catalog 32. |
| New inventory | Exactly three definitions and nine contracts. Current sorried totals: Embed 13, Seam 11, Catalog 32; total 56. |
| Elaboration log | Header records the full reported commit; exactly 56 `declaration uses 'sorry'` warnings, zero `error:` lines. Every warning's source line matches an attached theorem declaration. |
| Style log | Reports 0 FAIL and 9 size WARNs in the Turing-machine tree, including Catalog at 1012 lines; the other four campaign groups report 0 FAIL / 0 WARN. |

No fresh Lean build was run: neither `lean` nor `lake` is available in this workspace, and the packet is not a complete checkout. Fresh `.olean` production/timestamps and the actual repository commit association are therefore not independently reproduced. Internal diff/blob consistency is verified; it is not an external repository-history attestation. The separately cited decision-log/backlog entry justifying Catalog's size was not attached, so its recording is not independently verified.

The frozen context was used for configuration/action semantics, state mapping, capture/forwarding predecessors, and the named consumer seams. Tactic proofs, concurrent chapter repairs, and unchanged statements beyond what was needed to check these repairs were not re-audited. External bibliographic/licensing attestations from round 1 were not reopened; none is needed for the local counterexample or transition arguments here.

To close this gate, repair **both** through-halt theorem statements and replay the initially halted case explicitly. The other seven new contracts and R2–R10 need no mathematical weakening on this audit's evidence.

## Notation glossary

Lean identifiers and their bound variables retain their source meanings. Local explanatory notation:

- `d` in the counterexample: the silently transported starting configuration. In the compare count only, `d` instead denotes the first mismatch or word-end position, as in the repaired sketch.
- `q,r`: the two source states in S7; `start`, `exit`, `entry`, `done`: the respective phase controls in S9.
- `n`: total encoded-input length `|z|` in the R4 calculation; `a,b`: decoded first and second components.
- `A,B`: fixed administrative-space and total-time coefficients for the commissioned forwarding controller.
- `space_host`, `time_host`: the host's total visited-work-cell count at an arbitrary horizon and its completion time, respectively.
- `p`: first `false` position in successful increment, following the repaired sketch.
- `[-1,d]`, `[-1,p]`: sets of integer positions in the indicated inclusive intervals.
