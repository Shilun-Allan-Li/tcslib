External audit — fill campaign, Epoch 3
Intended repository path: `audits/epoch3-findings.md`

**Blocker: none identified. Major: none identified. Minor: one. Notes: eight.** These conclusions concern the supplied definitions, construction interfaces, and semantic invariants. They are not an independent Lean build certificate or blanket approval. Both architectural questions reserved in the plan remain for human disposition.

The primary input was `epoch3-bundle.md`, attributed to commit `b519a004`. Its SHA-256 is `432994488ab1e659001d995f4e2aa3d9f6a8bec4cdbe5eac63c3ab644afb30ca`. I extracted all 25 Lean modules and examined their actual definitions and invariant statements rather than accepting the agent reports. Line references below refer to the individual extracted files.

Supplementary checks used a pre-existing local Git baseline at `71721842a2336d5562ef831a19b0e86e063dddaa`, the earlier `36641745` refactor baseline, pinned Mathlib sources, and GitHub’s [comparison of the fill-span commits](https://github.com/Shilun-Allan-Li/tcslib/compare/71721842...b519a004). These checks are distinguished from evidence available in the attachment alone. Lean and Lake were unavailable; I did not rerun elaboration, `#print axioms`, or the amended style linter.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Encoding.lean` · `exists_effectiveMachineCode` docstring, lines 2199–2213 | No polynomial canonizer bound is claimed anywhere. | The retained sketch still says “with a polynomial `canonizerTime`” and names a composition-based construction. The implementation note explicitly supersedes that construction and disclaims polynomiality; the theorem itself imposes no polynomial bound. The appendix is honest, but the literal “anywhere” assertion is false, and the old paragraph can mislead when quoted alone. | Label the retained paragraph as the original, superseded proposed sketch. Preserve the implementation note and frozen theorem. This does not dispose of the architectural question or require a polynomial proof. |
| 2 | note | `Encoding.lean` · `codeParse`, `codeDecode_serialize_pad`, `codeCanonical_eq` | Parsing and compiled canonization implement the fixed grammar on every input. | Dictionary inverses, bounded indices, nested input-major/work-minor readers, exact record count, canonical count bits, and the all-true suffix test agree. The erased scanner is connected to the full parser on rejection as well as acceptance. Details below. | No correctness change identified. |
| 3 | note | `Encoding.lean` · `bridge_statement`, `bridge_compiles`, `bridge_binary` | Mathlib evaluation is transported to a finite binary machine with a uniform bound at each input length. | The stack representation, finite support, sentinel conversion, finite-reachability simulation, and alphabet-reduction application fit their contracts. The maximum ranges over finitely many input words, not arbitrary stack contents. | No correctness change identified. Retain the arbitrary-time qualification. |
| 4 | note | `Universal.lean` · `universal_lookup_parts`, `universal_prepare_next`, `universal_live_block`, `universal_from_blocks` | B2 closes the live block with the advertised enumeration, cursor invariant, and bound; the converse covers divergence. | The selected offset is three times the input-symbol index plus the work-symbol index. The final cursor lies on the selected record’s terminating zero, strictly before the serialization end. The exact ledger fits `3L + 5N + 20`. Positive block lengths and absorption establish the converse without eventual source halting. | No correctness change identified. |
| 5 | note | `Oblivious.lean` · `decorateTM_run`, `parallelTM_run`, `obliviousCandidate_decides` | Obliviousness holds at every physical time and preserves decision output. | Schedule projection and transverse coding are one-step correspondences. Data cannot choose physical movement or halt early. Source halting causes virtual idling; the schedule subsequently emits one answer and enters an absorbing native halt. The time and output certificates concern the same candidate. | No correctness change identified. |
| 6 | note | Specific questions 5–7 · zero budgets and constant `T` | The requested degenerate instances satisfy the theorem’s hypotheses. | Some do not: initialized halting at time zero is impossible; if `T` vanishes at any length, `DTIME T` is empty; and `TimeConstructible (fun _ => 1)` is false because its lower bound fails at length 2. These are failed hypotheses, not simulator counterexamples. | State the vacuity explicitly. Use a globally admissible positive bound with a clock witness for a nonvacuous theorem-level language test. |
| 7 | note | Freeze attestation; `Sweep.lean`; statement-prose amendments | The observed freeze is sound, although multiset comparison alone is insufficient. | Supplemental ordered comparisons found unchanged public headers and unchanged pre-existing declaration code except the three target proofs. Both prose fixes are comment-only. The 22 promoted Sweep declarations retain their code after removing comments and `private`; `indexedFold` retains `Nodup`, and `source_bounds` concerns initialized runs. A multiset alone cannot detect reordering. | Retain ordered declaration/signature comparisons alongside the multiset diagnostic. No statement repair identified. |
| 8 | note | `Universal.lean` · `timed_universal` | The remaining statement and sketch are implementable using B2’s infrastructure. | The inclusive deadline and nested pairing are coherent. New parsing, countdown, buffering, and delayed-halting invariants remain necessary. In particular, canonization must receive the original code alone, not the clock-dependent outer payload. | Carry these obligations into Epoch 4. The untimed assembly does not itself prove the timed theorem. |
| 9 | note | Repository attestations 2, 3, 5, 6 | Integrated elaboration, exact axiom footprints, lint results, and archive provenance were independently reproduced. | They were not. Sources and reports do not supply a working build environment, raw integrated logs, or the four archives/manifests. The narrower reproduced facts are listed below. | Preserve the distinction between source inspection and kernel/provenance evidence. Supply the corresponding environment and artifacts if independent reproduction is required. |

The principal contracts, read from the declarations, are:

- `exists_effectiveMachineCode`: existence of a padded-round-trip scheme whose decoded machine’s fixed serialization is computed by an in-model machine within some length bound. Neither polynomiality nor a particular public decoder is asserted.
- `universal`: one evaluator per effective scheme, with a representation-dependent constant uniform over input and source deadline, and both directions of the completed-output relation.
- `oblivious_of_mem_DTIME`: an unrestricted finite-tape binary decider whose represented head positions depend only on input length and physical time. No simultaneous one-work-tape normal form or output-head predicate is exported.
- `timed_universal`: an admitted deadline-inclusive evaluator, returning success exactly when the source halts by the deadline and otherwise returning timeout.

The following checks answer the specific questions and principal semantic priorities.

1. **Parser, empty input, padding, and the all-input canonization joint.**

   For the constructed scheme,
   \[
   \texttt{pairDecode []}=\texttt{none}
   \quad\Longrightarrow\quad
   \texttt{codeDecode []}=\texttt{codeFallback}.
   \]
   The fallback has one live state, initial index zero, stationary heads, no writes or emissions, and a halting successor on every read pair. It halts after one transition, not at initialization.

   Its serialization consists of the count delimiter, initial-state zero, and nine nine-bit zero records:
   \[
   \operatorname{serialize}(F)=[0,1]\mathbin{+\!\!+}0^{82},
   \qquad |\operatorname{serialize}(F)|=84.
   \]
   Bits 0 and 1 denote `false` and `true`. The empty count-bit list canonically represents zero.

   The guard examines the suffix after the count delimiter. For a valid code with \(N\) live states, initial index \(q_0\), and \(m\) padding bits,
   \[
   |\text{remaining suffix}|
   =(q_0+1)+|\text{table}|+m
   \ge1+81N+m>81N.
   \]
   Therefore the guard accepts valid codes with zero padding. `codeParse_serialize_pad` and `codeDecode_serialize_pad` quantify over every machine and padding length, including the fallback’s own serialization.

   The dictionaries distinguish no write from writing blank. State fields are range-checked; movement and output fields reject unused patterns. The outer `codeReadSymbols` selects the input symbol, and the inner reader selects the work symbol. `codeReadVec` consumes exactly the declared number of nine-record groups and short-circuits on failure. The guard bounds that number before recursion begins.

   Canonization does not merely strip trailing ones. Its decisive equations are
   \[
   \begin{aligned}
   \texttt{codeParse}\;xs
   &=\operatorname{map}(\mathrm{fst})(\texttt{codeParseFull}\;xs),\\
   \texttt{codeScan}\;xs
   &=\operatorname{map}(\mathrm{snd})(\texttt{codeParseFull}\;xs).
   \end{aligned}
   \]
   If the common parser fails, both routes produce the fallback serialization. If it returns \(\operatorname{some}(M,r)\), `codeParseFull_sound` gives
   \[
   xs=M.\mathrm{serialize}\mathbin{+\!\!+}r,
   \qquad
   xs.\mathrm{take}(|xs|-|r|)=M.\mathrm{serialize}.
   \]
   Thus `codeCanonical_eq` identifies the primitive-recursive function with serialization after decoding on **every** word, including arbitrarily long padding and oversized declared tables.

2. **Mathlib bridge and the finite maximum.**

   I checked the pinned [compiler interface](https://github.com/leanprover-community/mathlib4/blob/029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e/Mathlib/Computability/TMConfig.lean), [TM2 semantics](https://github.com/leanprover-community/mathlib4/blob/029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e/Mathlib/Computability/TuringMachine.lean), and [evaluation/support theorem](https://github.com/leanprover-community/mathlib4/blob/029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e/Mathlib/Computability/TMToPartrec.lean). `exists_code` supplies the vector-input/singleton-output contract used by `codePrim_machine`. `tr_eval` identifies the compiled result with the canonical halted configuration containing the output on its main stack.

   `bridgeStack` stores a stack in negative cells with its top at minus its length. Push moves left and writes; nonempty pop erases and moves right; empty pop stays at the blank origin. Finite control contains supported statements and a finite optional-symbol register. Unbounded values reside on tapes.

   The two-transition push and one-transition other-operation costs are **per primitive statement operation**, not per entire `TM2.step`. Mathlib’s `stepAux` recursively executes statement tails; `bridge_statement` correspondingly concatenates finite native runs. `bridge_simulate` transports finite reachability, which suffices here.

   The sentinel encoding satisfies
   \[
   \begin{aligned}
   \mathrm{Nat.bits}(\texttt{bridgeNumber}\;xs)
   &=xs\mathbin{+\!\!+}[\mathrm{true}],\\
   \texttt{bridgeUnnumber}(\texttt{bridgeNumber}\;xs)&=xs.
   \end{aligned}
   \]
   Empty words and trailing false bits therefore survive. The output phase delays emission by one bit and discards the high sentinel at the list terminator. The empty word emits nothing.

   For each input \(x\), `bridge_compiles` supplies a finite halting time \(t_x\). The maximum is
   \[
   H(n)=\max_{x\in\{\mathrm{false},\mathrm{true}\}^{n}}t_x.
   \]
   There are \(2^n\) inputs, including exactly one at \(n=0\). No maximum over arbitrary stack contents or configurations occurs. Each selected computation is finite, so this maximum is finite regardless of intermediate values.

   Alphabet reduction applies to the `Sum.inl` embedding and yields a binary machine with a bound that is a constant multiple of \(H(n)+1\). Neither polynomiality nor monotonicity is required or established.

3. **Last state group, record order, and final cursor.**

   Put \(N=M.\mathrm{numStates}+1\), \(L=|M.\mathrm{serialize}|\), and
   \(k=2|\mathrm{Nat.bits}(M.\mathrm{numStates})|+2\).
   `universalActions_lookup` covers all nine read pairs: blank–blank has offset zero and true–true offset eight.

   `universal_lookup_parts` decomposes the serialization into its header, \(q\) preceding state groups, the selected group’s preceding records, the selected record, and the remaining suffix. For \(q=N-1\), exactly the preceding \(N-1\) groups are skipped. Each erased unary state symbol accounts for nine records; at most eight records are then skipped within the selected group.

   Let \(P=P_g+P_b\) be those skipped bit lengths. If \(u\) is the number of ones in the selected successor field, the final cursor is
   \[
   h'=k+q_0+1+P+8+u.
   \]
   The record decomposition gives
   \[
   L=h'+1+|\text{remaining suffix}|,
   \qquad h'<L.
   \]
   This includes the last record, whose remaining suffix is empty, and proves the required \(h'\le L\).

4. **Successor copying, action application, ledger, and divergence.**

   Selection erases all old unary state symbols before rewinding to cursor one. A halting successor takes one preparation transition and copies nothing; no stale partial successor remains.

   For a live successor \(q'\), including \(q'=N-1\), the exact sub-ledger is
   \[
   1+(q'+1)+(q'+2)+1=2q'+5:
   \]
   live flag, copy plus terminator, rewind, and action application. The table cursor remains on the terminating zero and the state head returns to one.

   `universal_apply_record` establishes full configuration equality. It preserves explicit blank writes, emissions, work motion, successor halting, and clamped input movement. The marker supplies a virtual blank over the physical delimiter; outward moves at either virtual boundary are suppressed, and the physical input and marker heads move together.

   | Phase | Transitions |
   |---|---:|
   | Main dispatch | \(1\) |
   | Table rewind | \(h+1\) |
   | Count-prefix scan | \(k\) |
   | Initial-state skip | \(q_0+1\) |
   | Group selection, state rewind, within-group skip | \(2q+P+3\) |
   | Fixed fields | \(8\) |
   | Successor preparation | \(1\) if halt; \(2q'+4\) if live |
   | Apply action | \(1\) |

   Therefore
   \[
   \begin{aligned}
   d_{\rm halt}&=h+k+q_0+2q+P+16,\\
   d_{\rm live}&=h+k+q_0+2q+P+2q'+19.
   \end{aligned}
   \]
   Since \(h,k,P\le L\) and \(q_0,q,q'\le N-1\),
   \[
   \begin{aligned}
   d_{\rm halt}&\le3L+3N+13\le3L+5N+20,\\
   d_{\rm live}&\le3L+5N+14\le3L+5N+20.
   \end{aligned}
   \]
   Already-halted related configurations instead use a one-step absorbing block.

   `universal_block_run` supplies checkpoints at physical times \(v_j\), after \(j\) source steps, satisfying
   \[
   j\le v_j\le S+Bj.
   \]
   If the target halts by physical time \(r\), choose \(j=r\). Absorption preserves its completed output at \(v_r\ge r\); the checkpoint relation forces the source to be halted with the same output. This also refutes alleged source divergence. No fairness or eventual-halting assumption enters.

5. **C’s ledger and zero cases.**

   Here \(n=|x|\), \(U=T(n)\), \(B=(a+1)(U+1)\), \(R=3B\), \(\tau\) is the masked clock’s first halting time, \(w\) its output width, and \(p\) its final input position.

   Reset costs \((p-1)_{\mathbb N}+2\), using truncated subtraction. At \(p=0\), this is **two** transitions: a clamped left move and a right move. Since \(p\le n+1\),
   \((p-1)_{\mathbb N}\le n\), including empty input.

   The operational ledger sums to
   \[
   \begin{aligned}
   &1+\tau+((p-1)_{\mathbb N}+2)+(2n+4)\\
   &\quad +(U+1)(2w+(a+1)+4)
     +(14B+10)+B(6R+8)+1\\
   &=\tau+(p-1)_{\mathbb N}+2n+18
     +(U+1)(2w+(a+1)+4)+22B+18B^2\\
   &\le\tau+3n+18
     +(U+1)(2w+(a+1)+4)+22B+18B^2.
   \end{aligned}
   \]
   Using \(n\le U\), \(\tau,w\le b(U+1)\), and
   \(U+1\le(U+1)^2\), the coefficients become
   \[
   18(a+1)^2+
   \underbrace{(a+1)+22(a+1)}_{23(a+1)}
   +\underbrace{b+2b}_{3b}
   +\underbrace{3+18+4}_{25}.
   \]
   Thus the advertised constant is reproduced:
   \[
   c=18(a+1)^2+23(a+1)+3b+25.
   \]

   The length hypothesis also gives \(n+1\le B\) for copying, allocation, and support. Initialized work heads and nonblank cells lie within distance \(j\) after \(j\) source steps, giving relative displacement at most \(2j\). The copied input and boundary tags fit within \(n+1\). These bounds justify the radius-\(3B\) sweeps.

   If \(U=0\), then \(n=0\), but the administrative construction still has \(B=a+1\ge1\), an empty binary budget, and a defined final underflow. Its arithmetic permits zero multipliers. Genuine witnesses do not: \(a=0\) contradicts source halting, and \(b=0\) contradicts clock halting; `TimeConstructible` additionally requires \(b>0\).

   More strongly, any zero value of \(T\) makes `DTIME T` empty, as `DTIME_eq_empty_of_exists_zero` states. Thus the decision premise is impossible when \(T(0)=0\), even though the administrative zero-budget ledger remains valid.

6. **Every physical time, early halting, and binary coding.**

   The schedule tests actual input only for blankness. During the clock phase every nonblank read becomes false. `maskedClock_lockstep` identifies the complete masked run with the witness’s run on the constant word of the same length. `clockStageCfg_captures` connects that run to the actual schedule, including a final clock emission.

   `decorateTM` obtains all physical movements and its successor/halting decision from the schedule. Data supplies writes, finite data state, and output only. `decorateTM_step` and `decorateTM_run` give projection at every natural time; `decorateTM_heads` aligns every data head with the guide head.

   Transverse coding represents a nonblank symbol on simultaneous Boolean tracks and logical blank by all-blank tracks. No-write remains no-write, while writing blank erases all tracks. `parallelTM_step` and `parallelTM_run` give exactly one binary transition per logical transition. There is no unchecked interval between coding checkpoints.

   After source halting, virtual actions become identities while the remaining macrosteps continue. The payload invariants implement writes followed by head-relative shifts, including boundary clamping. The last-output register suffices because the source’s completed decision output is a singleton. The final counter test emits that saved bit once.

   **After the simulator itself halts, its configurations are absorbing; it does not continue sweeping.** The decoration and binary correspondences quantify over arbitrary \(t:\mathbb N\), including halted configurations. Hence head equality persists indefinitely. Output uniqueness validly combines the independent time and correctness certificates because they concern the same deterministic candidate.

7. **Requested adversarial instantiations.**

   | Instance | Result |
   |---|---|
   | Empty code and empty input through `universal` | The physical input is `[false,true]`. Extraction takes two steps and parks at physical position 3, the right blank. The virtual left boundary lies over delimiter position 2; virtual initial position 1 is the right blank. For the concrete 3A scheme, canonization produces the 84-bit fallback serialization and the simulated source halts silently after one step. For an arbitrary effective scheme, `decode []` need not be the fallback; startup correctly uses that scheme’s decoded machine. |
   | Initialized source halting at \(t=0\) | Impossible by `not_computesInTime_zero`; the public forward premise is false. Arbitrary already-halted checkpoints are nevertheless handled by the one-step absorbing block. |
   | Trivial machine through 3A | Its serialization parses with zero or arbitrary true padding; canonization returns the exact serialization. Sentinel conversion preserves its trailing zeros without emitting the sentinel. |
   | Length-one language with \(T\equiv1\) through 3C | The global theorem cannot be instantiated because time constructibility would imply \(2\le1\). The language containing only `[true]` does belong to `DTIME (fun _ => 1)`: inspect at most two cells, using multiplier 2. It is the clock definition’s global lower bound that fails. Local length-one layout inequalities cannot supply that missing global hypothesis. |

For the remaining timed theorem, the nested pairing has prefix length
\[
4|\mathrm{Nat.bits}(t)|+2|\alpha|+6,
\]
independent of \(x\). Budget zero still contains delimiters and must produce `[false]`; first halting on transition \(t\) must count as success.

B2’s finite interpreter, action correspondence, table invariant, and core block ledger can support the extension. Necessary new obligations are: separate the clock from \(\alpha\); send **only \(\alpha\)** to `c.canonizer`; buffer emissions; decrement once per simulated source transition; and intercept source halting before native halting so the success tag and buffer can be emitted. Canonizing the clock-dependent outer payload would decode the wrong machine and introduce an uncontrolled canonizer cost.

The additional countdown work is a constant multiple of
\((t+1)(|\mathrm{Nat.bits}(t)|+1)\); buffering and flushing concern at most \(t\) bits. Since \(|\mathrm{Nat.bits}(t)|\le t+1\), the quadratic allowance is consistent. This establishes implementability of the sketch, not the remaining Lean proof.

The repository-side attestations have the following status.

| Attestation | Reproduced from the attachment | Supplementary checks and remaining limits |
|---|---|---|
| 1. Freeze / drift | Public counts are Encoding 12, Universal 3, Oblivious 2. All newly identified handwritten fill declarations—138/104/238 respectively—are private. Both amended docstrings accurately describe their declarations. | Against the local baseline, exactly four of the 25 files differ. The stripped multiset loses only one `sorry` per target. Ordered comparisons find no other pre-existing declaration-code changes or public-header changes; all three Universal theorem headers are byte-identical. Halting’s code is unchanged. GitHub confirms exactly these four changed Lean paths repository-wide. I did not byte-compare every attachment against the remote head. |
| 2. Elaboration | Exactly one literal admission occurs after stripping nested comments: `Universal.lean:2463`, within `timed_universal`, whose declaration begins at line 2454. | **Not reproduced:** successful elaboration, zero errors, fresh-olean enforcement, warning count, or integrated-tree success. |
| 3. Axiom footprints | Static inspection locates the remaining admission in `timed_universal`; no replacement axiom or listed bypass mechanism appears in the supplied code. Relevant Mathlib interfaces were inspected at the stated pin. | **Not reproduced:** any exact `#print axioms` result or absence of transitive `sorryAx`. Importing an admitted theorem’s module does not itself establish dependency; a text scan cannot compute an axiom footprint. |
| 4. Soundness / imports | No `axiom`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, `@[extern]`, or `unsafe` token appeared in the comment-stripped 25-module scan. | Baseline comparison reproduces unchanged option headers, the stated import additions, four deriving clauses, and 14 explicit `decide` occurrences: Encoding 1, Universal 10, Oblivious 3. Their kernel checking remains conditional on elaboration. |
| 5. Policy / lint | Prose amendments are accurate. Line counts are Encoding 2263, Universal 2465, Oblivious 4086, SingleTape 981. Attached facades import the relevant supplied children; the plan records split escalations. | **Not reproduced:** the amended linter’s zero-FAIL/three-WARN execution, campaign-wide survey, or top-level export/build integration outside the supplied modules. |
| 6. Delivery provenance | Reports and continuation brief describe the claimed lineages and deliverables. Their statements were inspected, not accepted as provenance evidence. | **Not reproduced:** archive manifests, source/patch/bundle equivalence, complete parent/base preservation, preserved authorship, or agreement of original build/axiom logs. Those archives and raw logs are absent. |

The supplemental refactor comparison found 22 declarations promoted from SingleTape to Sweep with unchanged code after removing comments and `private`; no old public short name disappeared in the compared chapter modules. In particular, `indexedFold` retains its duplicate-free index hypothesis, and `source_bounds` applies to runs from `initCfg`, not arbitrary configurations.

Independent Python models additionally checked:

- 8,191 binary words of length at most 12; 600 padded round trips; 1,800 mutated serializations; three oversized headers.
- 4,860 universal live blocks covering the tested action-field combinations, all read pairs, both boundaries, empty input, maximal state/successor indices, and old cursors zero or serialization length.
- 264 decorated schedule executions from captured-clock endpoints in 66 parameter groups, checking represented payloads at each macrostep, exact transition counts, and head equality at every physical time across equal-length words, with executions up to 7,736 steps.

No counterexample appeared. These are finite diagnostics, **not Lean executions or proofs for unbounded inputs**. The arbitrary-time post-halting argument rests on the source correspondences and absorption.

Notation glossary: \(F\) is the fallback machine; \(xs\) a binary word and \(r\) a parser suffix; \(+\!\!+\) denotes concatenation and \(|\cdot|\) length; \(H(n)\) is the bridge’s finite maximum and \(t_x\) a selected halting time. For B2, \(N\) is the live-state count, \(L\) serialization length, \(k\) count-prefix length, \(q_0,q,q'\) initial/current/successor indices, \(h,h'\) old/new table cursors, \(P_g,P_b,P\) skipped bit lengths, \(u\) successor one-count, and \(d\) block duration. For assembly, \(S,B\) are startup/block bounds and \(v_j\) the checkpoint time after \(j\) source steps. For C, \(n,U,a,b,\tau,w,p,B,R,c\) denote input length, \(T(n)\), decider/clock multipliers, clock halting time, clock width, clock endpoint, macrostep budget, guide radius, and final time constant. \((p-1)_{\mathbb N}\) is truncated subtraction. \(\alpha,x,t\) are code, input, and source deadline.
