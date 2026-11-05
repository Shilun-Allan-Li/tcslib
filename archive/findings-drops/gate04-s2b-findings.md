# Gate 04 — S2b external audit findings

**Verdict: DO NOT CLOSE.**
**0 blockers, 2 majors, 4 minors.**

F01 and F02 prevent closure under the pack’s zero-major criterion. The two explicitly deferred efficiency proofs are not counted as findings merely for containing `sorry`.

**Audited head:** `afe5982f612081bba2fbcec9ab41adcbbc118b13`, PR #195.
**F-1 baseline:** `a3c5fa8b72e50939822f22364647dc844a3914a0`.
**Bundle:** 45 sections; computed SHA-256 `d64276ef3bec3f2f7d67fb5d2162b0034422710fc878bb2c158e14831c4c079a`. No expected bundle digest was supplied.
**Source PDF:** A Course in Cryptography, third edition, January 2010; SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.
**Pagination:** book page = PDF page − 12.

Paths below are relative to `TCSlib/Cryptography/`, except campaign records and explicitly identified dependencies. Line numbers refer to individual Lean files.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F01 | Major | `Games/BitCodec.lean:60–61,76–93` · `decodeIdx`, `decodeBitMove` | The accepted query format uses the unary index `1^i`; other malformed moves produce the default output. | `decodeIdx 2 [false] = some ⟨1, …⟩`: only length is tested. An otherwise correctly paired query with index word `[false]` and a correctly sized payload queries oracle 1 instead of returning the default. Forward round-trip theorems cannot detect this. | Check that every index bit is `true`, as well as checking its length. Publish a converse characterizing successful index decoding by `iw = List.replicate i true`, and a converse characterization of accepted queries. |
| F02 | Major | `Games/Machines.lean:89,97,122,135`; `Games/Efficiency.lean:86–108,171–194`; bridges below | This is a published API suitable for subsequent statements and fills under the bundled repository policy. | Important definitions have bounds or forward examples but lack complete defining equations. Cross-file consumers compensate: `Bridges/Machines.lean:65` unfolds `MachineCodec.encodeLog` and `encodeHist`; lines 79/82 unfold `buildComp` and `buildTree`; line 108 unfolds `NUPPT.toComp` and `toOracleAdversary`. `Bridges/Strategies.lean:183` unfolds `Protocol.outP`, `outV`, and `transcriptWith`. This conflicts with the publication/no-unfolding standard in bundled `policy.md` §1. | Publish complete case/defining equations and relevant codec projections, then make bridges consume them. Cover log nil/cons, both builder-budget cases, both machine decoders, handler input/answer/implementation, interactive call/implementation, and the D8 equations used by B4. Reuse existing equations where sufficient. A cost bound is not a defining equation. |
| F03 | Minor | `Games/Efficiency.lean:93–100` · `PolyHandler.answer` | A malformed output gives the all-false answer and state. | With both lengths 1, a constant handler returning `pairEncode [true] []` gives answer `true` and state `false`. Conversely, `pairEncode [] [true]` gives answer `false` and state `true`. Components default independently after successful pair parsing. | Document the componentwise default, or reject the whole pair whenever either component has the wrong length. Expose the chosen behavior through equations. |
| F04 | Minor | `Games/Efficiency.lean:145–150,175–185` · `InteractiveHandler`, `call` | One call uses at most `perCall(n)` rounds of `run`. | `buildComp` inspects a next move even at zero remaining query budget. A call with `perCall=0` runs the handler to obtain a return or timeout; a call making `p` queries can inspect `p+1` next moves. | Say “at most `perCall(n)` outer queries, with at most `perCall(n)+1` handler activations.” T2’s outer-query product remains correct. |
| F05 | Minor | `pack.md` · attestation 3; `evidence/axioms.log` | Every theorem in the 22 changed files was printed: 236 theorems, 234 clean and two admitted. | The files contain 251 explicit theorem declarations: 237 public and 14 private. The log has 237 named entries, including `uprob_update_absorb'`; two mention `sorryAx`. Private declarations are not individually enumerated. | Correct the public counts to 237 entries, 235 without `sorryAx`, and two with it. State the public/private scope; print the 14 private declarations if “every theorem” is intended literally. This is evidence accounting, not evidence of another admitted proof. |
| F06 | Minor | `Asymptotic/MultiMessage.lean:148,469`; `Asymptotic/MultiMessageLemmas.lean:300,379,629`; inherited definition descriptions below | Several inherited descriptions promise more than their formal statements expose. | The query-count theorem proves an upper bound, not exactness; the history projection theorem gives only the query component; the query-chain theorem exposes evaluation agreement, not an exact query sequence. The malformed-ciphertext description exceeds its projected-length premise at `n=0`. The block lemma is public despite “private copy” wording. These discrepancies predate F-1. | Narrow descriptions to the conclusions and premises, or publish stronger exact-count, answer-projection, syntax-rejection, and transcript statements where needed. Correct the visibility description. Do not classify these as F-1 semantic regressions. |

## Scope and verification limits

The audit brief was read first. New API bodies were inspected in comment-stripped form; the definition inventory below records their actual behavior independently of the documentation.

Every explicit theorem in the 22 changed files has an individual statement/docstring assessment: 251 entries, including private helpers. Three supplied context modules add 40 assessments. The pre-F1 copies were compared as baselines, not counted twice.

New proof bodies were checked by source-level reasoning. The F-1 check uses complete textual diffs and a semantic transport argument; it is not a fresh proof audit of every unchanged chapter 2–4 result. Bundled policy and design notes were assessed as submitted material, not taken as proof that planned work exists.

The imported machine, pairing, bit-decoding, and D8 definitions needed to interpret the contracts were inspected at the exact audited commit:
`Complexity/Randomized/PPT.lean`,
`Complexity/TuringMachine/Encoding.lean`,
`Cryptography/Asymptotic/Adversary.lean`,
and `Cryptography/ZeroKnowledge/Interaction.lean`.

**No independent Lean build or kernel replay was performed.** No Lean executable was available, and the execution environment subsequently became unavailable. Executable checks below are independent finite JavaScript models of the displayed recursive definitions, not compiled Lean counterexamples or proofs of T1/T2.

The supplied replay contains 772 distinct module-result records, all reporting zero errors, and records two admissions for `Games/Efficiency`. Its opening header names the earlier merge `827ad8e…`, whereas the axioms and lint headers name the audit head. The replay began before the final T2 commits and continued afterwards; its text alone is not a source-hash certificate for every invocation. Preserve source/olean provenance when refreshing evidence. The old header alone does not establish a failed replay.

## Required checks

### F-1: meaning preservation

**Result: no semantic change found at universe zero.** The restriction from arbitrary universes to `Type` is disclosed. Replacing an inductive type with an abbreviation changes automatically generated recursor APIs; `QueryTree.induct` supplies a compatibility interface. This is distinct from changing the mathematical adversary model.

Define transport from the old tree recursively:

\[
\begin{aligned}
T(\operatorname{ret}_{old}(a))&=\operatorname{pure}(a),\\
T(\operatorname{query}_{old}(x,k))
 &=\operatorname{query}((),x,\lambda y.\,T(k(y))).
\end{aligned}
\]

Define the inverse:

\[
\begin{aligned}
U(\operatorname{pure}(a))&=\operatorname{ret}_{old}(a),\\
U(\operatorname{query}((),x,k))
 &=\operatorname{query}_{old}(x,\lambda y.\,U(k(y))).
\end{aligned}
\]

Structural induction and function extensionality give

\[
U(T(t))=t,\qquad T(U(c))=c.
\]

There is no additional oracle choice: every `Unit` index is `()`.

The same induction gives

\[
\begin{aligned}
\operatorname{eval}_{new}(T(t),f)
 &=\operatorname{eval}_{old}(t,f),\\
\operatorname{BoundedBy}_{new}(T(t),q)
 &\Longleftrightarrow\operatorname{BoundedBy}_{old}(t,q),\\
T(\operatorname{simulate}_{old}(\pi,\mathrm{ans},t))
 &=\operatorname{simulate}_{new}(\pi,\mathrm{ans},T(t)),\\
\operatorname{evalLazy}_{new}(a,T(t),L)
 &=\operatorname{evalLazy}_{old}(a,t,L).
\end{aligned}
\]

For boundedness, split the query case into `q=0` and `q=q'+1`: both versions respectively reject or quantify over every continuation. For lazy sampling, `noteQuery` and position selection have identical bodies; they choose the same answer and updated history. Induction on the budget similarly transports `buildTree`.

Apply `T` pointwise to an adversary’s tapes. This bijection preserves every oracle evaluation and hence the event counted by `oracleDist`, `acceptProb`, and `prfAdv`. Machine constructions retain the coins, history encoding, move decoder, budget, and timeout. Thus the unchanged quantifiers in `OracleEnsemble.Indist` and `PRF` retain their security meaning.

| Restated file | Complete-diff assessment |
|---|---|
| `Pseudorandom/Functions/OracleAdversary.lean` | Representation becomes the one-oracle abbreviation; constructor wrappers and `induct` are added. Evaluation, boundedness, simulation, tape quantification, and distinguishing events retain their recursive meaning. |
| `Pseudorandom/Functions/LazySampling.lean` | Universe changes, three induction-interface changes, and a namespace/variable reset; sampling and stream-update bodies are unchanged. Repeated queries still reuse their first answer. |
| `Pseudorandom/Functions/Defs.lean` | Relevant query/answer variables become `Type`; the advantage expression is unchanged. Explicitly polymorphic `randomFunction` remains polymorphic. |
| `Pseudorandom/Functions/SubHybrids.lean` | Relevant table/seed/value types become `Type`; no probability, index, or challenge branch changes. |
| `Pseudorandom/Functions/GGM.lean` | Label type becomes `Type`; no walk, hybrid, or advantage formula changes. |
| `Asymptotic/PRF.lean` | Only the universe binders of `oracle_hybrid_lemma` change directly. Other declarations, including machine and security definitions, are textually unchanged and use the transported semantics. |
| `Asymptotic/PRFLemmas.lean` | Only the universes of `walk` and `ggmFrom_eq_walk` change. |
| `Asymptotic/MultiMessage.lean` | Only the universes of `chainTree` and its two elementary lemmas change. |
| `Asymptotic/MultiMessageLemmas.lean` | Only query/answer universe binders of two coin-relabelling lemmas change. |
| `Games/OracleComp.lean` | Existing computation model is unchanged. `singleSpec` and output-invariant API are added; `AllOutputs` and its monotonicity/bind laws retain their previous meaning from `Hopping`. |

The design note proposed redefining `toOracleAdversary` through `toComp`. The implementation retains the old builder and proves `toComp_singleCodec`. That equality suffices for meaning preservation; the design note is not the actual definition.

### Codec: exact grammar, defaults, and bounds

For `k=2`,

\[
\operatorname{decodeIdx}(2,[\mathrm{false}])
 =\operatorname{some}(1),
\qquad [\mathrm{false}]\ne[\mathrm{true}].
\]

If oracle 1 has one-bit inputs,

\[
\operatorname{decodeBitMove}
 \bigl(\operatorname{pairEncode}[\mathrm{false}]
   (\operatorname{pairEncode}[\mathrm{false}][\mathrm{false}])\bigr)
 =\operatorname{query}(1,[\mathrm{false}]),
\]

where the right-hand payload denotes the corresponding one-bit function. This violates the documented malformed-move fallback.

This defect does not create an out-of-range index, shorten the index needed to reach oracle `i`, or bypass the query counter. Accepted aliases still have length `i<k`; a query still costs one. The same action can be emitted canonically. F01 concerns exact format fidelity, not a claimed new cryptographic attack.

Other checks:

- Pair parsing is exact: the pinned pairing API supplies `pairDecode_pairEncode` and the converse `eq_pairEncode_of_pairDecode`.
- `decodeFin` checks length equality, including zero. Wrong payload lengths and malformed tags take the return default.
- `k=0` admits no query. A zero-length output has one possible value.
- The all-false default can satisfy a game’s success predicate. It is a fixed legal output, not automatic rejection. A game requiring a distinguishable failure must represent one.
- Canonical log entries are injective under nested pairing and explicit index encoding.

For an entry at index `i`,

\[
\operatorname{length}(\operatorname{encodeEntry}(i,x,y))
 =2i+2\,\mathrm{din}(i)+\mathrm{dout}(i)+4.
\]

Its contribution to the nested log length is

\[
4i+4\,\mathrm{din}(i)+2\,\mathrm{dout}(i)+10.
\]

A polynomial budget and the supplied polynomial lengths therefore give a polynomial log bound. There is no compressed-unary length attack.

### T1 and T2: scope and remaining obligations

The statements are nonvacuous candidate closure contracts. No counterexample to either mathematical conclusion was found. Their admissions still require machine constructions and correctness proofs.

| Required item | Assessment |
|---|---|
| Genuine machine `B` | Both conclusions quantify `B : NUPPT`, containing a finite Turing machine and global polynomial halting bound. |
| Bijective coin split | The equivalence relates the full product of fixed handler seed and `A.Coins n` to `B.Coins n`. It precedes quantification over `z,ω,r`, so cannot depend on the reduction input. |
| Uniform probability transfer | A bijection on these finite nonempty bit spaces preserves the uniform product distribution. Efficient external computation of the bijection is unnecessary for that argument. |
| Output correspondence | T1 identifies simulation with a pure pair whose first component is `padFin dα (B.runAt …)`. T2 equates the complete output-projected outer computation with `B.toCompOn`, not just evaluations against deterministic oracles. |
| State and history size | State, seed, query, answer, and output lengths are explicit polynomials. The oracle-index set is fixed and finite. History size follows from the calculation above. |
| Arbitrary initial-state family | Permitted by non-uniformity: the polynomial-length `List.ofFn (H.init n)` can be placed in advice with `A.advice n`. No uniform-computability premise on `init` is missing here. |
| Arbitrary external input `z` | The pinned machine bound is polynomial in the complete encoded input, hence in `n+z.length`. Applications claiming time polynomial in `n` alone must establish their input-length bound. |
| Outer budget | At most `q(n)` inner calls, each making at most `perCall(n)` outer queries, justify the product, including zero factors. |
| Finalization at zero budget | `buildComp` inspects a final move at zero fuel. It returns a completed answer or defaults an attempted extra query without making an extra outer query. |

A feasible construction route is to concatenate the handler seed and adversary tape, include the bounded initial state in advice, and replay deterministic interaction against the supplied outer log. Between outer queries there are at most `q(n)+1` adversary activations and `q(n)·(perCall(n)+1)` handler activations. Retained state and histories are polynomially bounded; each handler input has length polynomial in `n+z.length`.

A guarded total parser/loop is still required on malformed raw machine inputs. This construction outline is not a substitute for the admitted Lean proofs.

Exact limitations:

1. The simulated adversary is `A.toComp`, without an external adversary input. The handler receives `z`. Applying the theorem to a phase using `A.toCompOn` requires an extension or a proved wrapper.
2. Final handler state is hidden: existential in T1 and projected away in T2. Postprocessing a forgery together with a query log needs an exposed computation or a proved finalization wrapper.
3. T1 promises normalized fixed-length output, not exact-length raw output. Strict inverter/verdict decoders may require an efficient normalization wrapper.
4. Neither statement promises a uniform `B`.

These are scope limitations, not counterexamples. The MAC reduction at book pp. 134–135 checks the final forgery and freshness; the two-phase encryption experiment at p. 168 passes a challenge and state into phase two. Wrappers/extensions and budgets must be exhibited before claiming T1/T2 alone implement those entire reductions. Possible missing future prongs are not counted as additional present majors.

### B4 and trace invariants

The imported D8 definitions give

\[
\begin{aligned}
\pi.\mathrm{outP}
 &=\pi.P.\mathrm{next}\;x\;y\;r_P\;
      (\pi.\mathrm{transcriptWith}\;\pi.P\;\cdots).1,\\
\pi.\mathrm{outV}
 &=\pi.V.\mathrm{next}\;x\;z\;r_V\;
      (\pi.\mathrm{transcriptWith}\;\pi.P\;\cdots).2.
\end{aligned}
\]

The displayed tapes mean their encoded lists.

The invariant used by `exec_turnParty` is

\[
\operatorname{Party.exec}\;k\;
  (\operatorname{turnParty}\;nF\;k\;MF)\;
  (\operatorname{waitParty}\;nG\;k\;MG).
\]

- At `k=0`, the active party returns `nF MF`; the peer receives `none` with waiting budget zero and returns `nG MG`.
- At `k+1`, the active party sends `nF MF`. The peer receives it with positive schedule, appends it, and becomes `turnParty nG k`. The original party becomes `waitParty nF k`.
- The invariant therefore holds with roles exchanged.
- Neither `none` with positive remaining schedule nor `some` with zero remaining schedule is reached. These off-schedule defaults do not affect embedded pairs.
- `exec_eq_alt` identifies final received histories with D8’s. `exec_strategies` yields `.done outP outV` or `.done outV outP` according to the first mover.

`execT_trace` separately proves pathwise invariants for arbitrary parties: total delivered messages are bounded by fuel; the second mover receives equally many or one more; `outOfFuel` implies exact fuel consumption.

B4 is a fixed-tape output bridge. The further planned sampled `Strategy.toParty`, exact D8 view projections, and equality of joint view/output distributions are not implemented here. Book pp. 115–116 and 155–156 require complete tapes and received messages for views. Those additional claims remain pending.

### Adversarial instantiations

| Instantiation | Calculation or executed check | Result |
|---|---|---|
| Non-unary index | `decodeIdx 2 [false]` yields index 1; embed it in an otherwise valid query. | F01. |
| Exhaustive small raw moves | Checked all 131,071 words of lengths 0–16 with `din=[0,1,2]` and output length 2 against the documented strict-unary grammar. | 14 mismatches, all non-unary aliases. Separately, 151 canonical query/return round trips passed across small dimensions. |
| Log collisions and lengths | Enumerated 259 logs of length at most 3 for two small typed oracles. | No encoding collision or length discrepancy. |
| One malformed handler component | Lengths 1 and 1; outputs `pairEncode [true] []` and `pairEncode [] [true]`. | Valid component survives; F03. Constant handlers satisfy efficiency premises. |
| Zero outer budget | `perCall=0`; immediate return supplies an answer, attempted query forces default. | Supports T2’s zero-product case; refutes the zero-activation reading of F04. |
| Simulation/replay | 240 finite cases: inner budgets 0–3, per-call budgets 0–2, seeds, early stops, and budget-overrun attempts. Compared full branching output trees. | All matched; 120 cases had a zero factor. Not a machine-level or universal verification. |
| Mover order and parity | 936 deterministic executions: six next-message functions per party, both orders, and 0–12 messages. Compared D8 outputs and received histories. | All matched; no off-schedule default reached. |
| Empty sample space | Old `uprob` gives 0/0=0 even for `True`; game sampling requires `Nonempty`. | B2’s nonemptiness hypotheses are necessary. |
| Malformed ciphertext at zero | Ciphertext `[]` has two default projections of length zero; `prfDecWF` accepts at `n=0`, decryption returns `[]`, and `decodeFin 0` accepts. | The failure theorem’s premise is false; its description, not its statement, is overbroad (F06). |
| Constant query-chain distinguisher | An always-rejecting distinguisher can be matched by a suitably taped machine that rejects without querying. | Evaluation equality alone does not expose the claimed query sequence (F06). |

The first, fourth, fifth, eighth, ninth, and tenth rows are direct mathematical instantiations. Finite enumeration supports the other rows, without replacing structural arguments.

The inherited work descriptions for `SubHybrids.tableDist` and `GGM.ggmDist` also need “when `A.BoundedBy q`” (F06). Their definitions accept arbitrary trees and do not stop them after `q` queries; exhausted answer arrays still have fixed extensions. Relevant bounded endpoint/security theorems supply the missing qualification.

## Independent definition restatements

These are the 58 new, moved, or universe-affected definitions relevant to S2b/F-1. Unchanged definitions are not relabelled as new.

### Games/Machines.lean

| Declaration | Code-based restatement |
|---|---|
| `Move` · 66 | A choice between an indexed, correctly typed query and a final value. |
| `MachineCodec` · 75 | Three unconstrained operations: decode an output word as a move, encode a typed log entry, and choose a timeout value. Faithfulness and efficiency are not fields. |
| `MachineCodec.encodeLog` · 89 | Fold an ordered log into nested pairs, terminated by the empty word. |
| `buildComp` · 97 | Inspect successive moves; return final values, append query-answer entries with positive fuel, and default attempted queries at zero fuel. |
| `NUPPT.toComp` · 122 | Fix the machine tape, rerun the machine on each encoded history, and build a bounded computation from empty history. |
| `NUPPT.toCompOn` · 135 | The same construction, supplying every activation the paired explicit input and history. |

### Games/BitCodec.lean

| Declaration | Code-based restatement |
|---|---|
| `bitSpec` · 56 | A finite oracle family with bit-function queries and answers of prescribed lengths. |
| `decodeIdx` · 60 | Accept any word shorter than `k`, using its length as index and ignoring bit values. |
| `zeroBits` · 71 | The constant-false bit function of the requested length. |
| `decodeBitMove` · 76 | Parse tag and payload; accept queries after nested parsing, index decoding, and exact query-length decoding; decode exact-length returns; otherwise return all false. |
| `bitCodec` · 97 | Combine that decoder with canonical unary-index log entries and all-false timeout. |

### Games/Bridges/QueryTree.lean

| Declaration | Code-based restatement |
|---|---|
| `OracleComp.evalFn` · 64 | Follow branches selected by deterministic oracle functions to the returned value. |
| `treeImpl` · 91 | Translate each inner query into one outer query, convert its answer, and preserve state. |

### Games/Bridges/Experiments.lean

| Declaration | Code-based restatement |
|---|---|
| `acceptGame` · 107 | Independently sample sampler seed and distinguisher tape from nonempty finite types, then return the Boolean result. |

### Games/Bridges/Machines.lean

| Declaration | Code-based restatement |
|---|---|
| `singleCodec` · 45 | Reuse the old single-oracle decoder and entry representation, with false timeout. |
| `toHist` · 54 | Discard the sole Unit oracle label while preserving ordered query-answer pairs. |

### Games/Bridges/Strategies.lean

| Declaration | Code-based restatement |
|---|---|
| `Msg` · 64 | Bit words used as messages. |
| `turnParty` · 69 | At zero remaining messages return `next` on received history; otherwise send that value, then close or resume after appending scheduled input. |
| `waitParty` · 80 | On `none`, return `next` on current history. Append scheduled input and activate the next turn; discard incoming input when schedule is already zero. |
| `alt` · 95 | Compute received histories by sending, swapping roles, recursively executing remaining messages, then swapping results back. |

### Games/Efficiency.lean

| Declaration | Code-based restatement |
|---|---|
| `bitSpecAt` · 62 | Evaluate query/answer length polynomials at the parameter. |
| `PolyHandler` · 69 | Polynomial-time string function, polynomial state/seed lengths, and arbitrary initial-state family. |
| `PolyHandler.input` · 86 | Encode unary parameter, external input, seed, state, unary oracle index, and query in the prescribed nested layout. |
| `PolyHandler.answer` · 93 | Run once, parse an answer/state pair, and default each failed component separately. |
| `PolyHandler.impl` · 105 | Answer deterministically with the computed answer/state pair, without sampling queries. |
| `InteractiveHandler` · 151 | Add an outer oracle family and polynomial per-call query budget to the seeded stateful next-move mechanism. |
| `InteractiveHandler.input` · 171 | Encode ordinary handler inputs together with the current outer-query log. |
| `InteractiveHandler.call` · 178 | Build a bounded outer computation from empty per-call history, returning concatenated answer/state or all-false timeout. |
| `InteractiveHandler.impl` · 190 | Run that computation and split its returned bits at the answer length. |

### Games/OracleComp.lean

| Declaration | Code-based restatement |
|---|---|
| `singleSpec` · 155 | Give one oracle the Unit index type and supplied query/answer types. |
| `AllOutputs` · 268 | Require the predicate at returns and recursively for every answer continuation at queries. It does not claim an empty-range oracle can answer. |

### Pseudorandom/Functions/OracleAdversary.lean

| Declaration | Code-based restatement |
|---|---|
| `QueryTree` · 82 | Abbreviate free oracle computation over `singleSpec`, at universe zero. |
| `ret` · 89 | The framework’s pure constructor under the old leaf name. |
| `query` · 92 | The query constructor with Unit index. |
| `induct` · 97 | Eliminate into a Sort-valued motive from leaf and query cases with all subtree hypotheses. |
| `eval` · 103 | Follow a deterministic oracle’s chosen branches to a leaf. |
| `BoundedBy` · 117 | Accept leaves at any budget, reject queries at zero, and require all continuations to fit predecessor budget. |
| `simulate` · 150 | Translate each query, convert the outer answer, and recurse. |
| `OracleAdversary` · 179 | A tape-indexed family of Boolean trees; probability functionals impose finite uniform tapes separately. |
| `OracleAdversary.BoundedBy` · 183 | Require the bound at every tape. |
| `oracleDist` · 191 | Evaluate the selected tape’s tree against the supplied function. |

### Pseudorandom/Functions/LazySampling.lean

| Declaration | Code-based restatement |
|---|---|
| `noteQuery` · 126 | Preserve history for an existing query; otherwise append it. |
| `evalLazy` · 150 | Use the answer-stream position of the query’s first occurrence in updated history; do not deduplicate arbitrary initial history. |

### Pseudorandom/Functions/Defs.lean

| Declaration | Code-based restatement |
|---|---|
| `prfAdv` · 67 | Absolute acceptance gap between uniform keyed function and uniform full table, with the same adversary coins. |

### Pseudorandom/Functions/SubHybrids.lean

| Declaration | Code-based restatement |
|---|---|
| `subHybridStream` · 76 | Uniform-value prefix followed by generator images of a seed stream, retaining fixed out-of-range extension. |
| `lazyDist` · 81 | Evaluate the tape-specific tree lazily from empty history. |
| `subHybridProb` · 88 | Average over finite arrays and coins without imposing a query bound in the definition. |
| `challengeStream` · 93 | Replace one selected sub-hybrid position by the challenge. |
| `tableDist` · 107 | Run against that challenge stream; its advertised bounded work needs a separate adversary bound. |

### Pseudorandom/Functions/GGM.lean

| Declaration | Code-based restatement |
|---|---|
| `pairSel` · 74 | Choose first component for false, second for true. |
| `ggmFrom` · 80 | Expand and select children from position `i`, stopping at or beyond depth `n`. |
| `ggm` · 96 | Start the walk at zero from the supplied key. |
| `hybridOracle` · 107 | Read a prefix label from a table and finish the walk. |
| `hybridProb` · 112 | Average acceptance over the uniform prefix table and adversary tape. |
| `levelAdv` · 137 | Query the level prefix, select the relevant returned child, finish the walk, and answer the original tree. |
| `ggmDist` · 199 | Apply the table-challenge distinguisher to `levelAdv`; bounded work requires a bound on the adversary. |

### Asymptotic/PRFLemmas.lean

| Declaration | Code-based restatement |
|---|---|
| `walk` · 287 | Fold child selection over the supplied bit list from the supplied label. |

### Asymptotic/MultiMessage.lean

| Declaration | Code-based restatement |
|---|---|
| `chainTree` · 86 | Query tuple positions in increasing order and apply the supplied function to the answer tuple. |

## Theorem-by-theorem statement review

“Matches” means the formal statement expresses the documented claim with its written hypotheses. It does not mean an independent kernel check or completion of an admitted proof.

The first 22 groups contain 251 theorem declarations. The last three context modules contain 40. Pre-F1 versions are covered by their current rows and the preservation analysis.

### Asymptotic/MultiMessage.lean

| Declaration | Statement versus docstring |
|---|---|
| `eval_chainTree` · 92 | Matches querying the tuple in order and applying the supplied result function. |
| `boundedBy_chainTree` · 110 | Matches the upper bound equal to chain length. |
| `multiMsgAdv_boundedBy` · 148 | Proves at most `q+1`, not the documented exact count; F06. |
| `acceptProb_oracleDist_multiMsgAdv` · 156 | Matches the acceptance identity with the real-ciphertext sampler. |
| `prfAdv_multiMsgAdv` · 171 | Matches the first hybrid gap with the corresponding PRF advantage. |
| `uprob_not_injective_le` · 192 | Matches the birthday bound with the disclosed corrected binomial coefficient. |
| `pushesUniform_comp_injective` · 231 | Matches uniformity of restriction to distinct points. |
| `distAdv_prfEncReal_random_otp_le` · 269 | Matches the random-function/independent-pad gap bounded by collision probability. |
| `acceptProb_otpEnc` · 308 | Matches equality for message vectors under independent uniform pads. |
| `distAdv_prfEncReal_le` · 343 | Matches two PRF gaps plus twice the collision bound. |
| `polyTimeComputable_prfEncFun` · 403 | Matches efficient encryption from an efficient evaluator. |
| `polyTimeComputable_prfDecWF` · 416 | Matches efficient projected-length checks. |
| `polyTimeComputable_prfDecFun` · 432 | Matches efficient guarded decryption. |
| `runAt_prfEnc` · 448 | Matches the exact encryption activation. |
| `runAt_prfDec` · 458 | Matches decryption under both component-length assumptions. |
| `decodeFin_runAt_prfDec_of_not_wf` · 469 | Covers wrong projected lengths, not every malformed pair at zero; F06. |
| `zipWith_xor_xor_self` · 486, private | Matches repeated-pad cancellation when the pad is sufficiently long. |
| `encodeList_eq_flatMap` · 526, private | Matches concatenated self-delimited chunks. |
| `encodeTuple_eq_flatten` · 535 | Matches flattened tuple encoding. |
| `prfScheme_multiEncDist` · 543 | Matches the constructed scheme’s encoded hybrid sampler. |
| `prfScheme_multiMessageSecure` · 597 | Matches multi-message security under PRF security. |
| `exists_multiMessageSecure_of_prf` · 655 | Matches existence from a PRF. |
| `exists_multiMessageSecure_of_exists_prg` · 662 | Matches existence from a secure PRG via GGM. |

### Asymptotic/MultiMessageLemmas.lean

| Declaration | Statement versus docstring |
|---|---|
| `abs_uexp_le_uexp_abs` · 77 | Matches the triangle inequality for finite averages. |
| `abs_uexp_sub_le_uprob` · 89 | Matches the bad-event bound for [0,1]-valued tests agreeing outside that event. |
| `card_filter_lt_pairs` · 108 | Matches the binomial count of pairs with first index smaller. |
| `uprob_eq_pair` · 139 | Matches reciprocal-cardinality collision probability on a nonempty type. |
| `negligible_choose_div_two_pow` · 157 | Matches negligibility of the polynomial birthday term over `2^n`. |
| `acceptProb_oracleDist_congr_equiv` · 188 | Matches acceptance preservation under bijective tapes and pointwise evaluations. |
| `prfAdv_congr_equiv` · 200 | Matches the corresponding advantage preservation. |
| `length_histBlock` · 217 | Matches exact length `6n+6`. |
| `encodeHist_eq_flatMap` · 223 | Matches fixed-width history blocks. |
| `eval_histBlockLen` · 235 | Matches evaluation of the block-length polynomial. |
| `length_flatMap_of_length` · 238 | Matches total length for equally sized outputs. |
| `flatMap_range_blocks` · 256 | Matches block extraction/mapping with positive width. |
| `flatMap_const_singleton` · 284 | Matches unary counting of list elements. |
| `flatMap_const_replicate` · 292 | Matches unary multiplication by constant block length. |
| `pairFstD_pairFstD_histBlock` · 300 | Gives the query projection only; documentation promises both components, F06. |
| `length_maskBlock` · 311 | Matches the history-block length. |
| `dbl_append` · 317 | Matches doubling’s preservation of concatenation. |
| `zipWith_xor_replicate_false` · 321 | Matches XOR with same-length zeros. |
| `zipWith_xor_dbl` · 329 | Matches commuting XOR with doubling, including truncation. |
| `zipWith_xor_histBlock_maskBlock` · 343 | Matches unchanged query and masked answer in the encoded block. |
| `zipWith_xor_flatten_ofFn` · 367 | Matches chunkwise XOR under corresponding-length equalities. |
| `take_drop_ofFn_blocks` · 379 | Matches in-range extraction; public despite “private copy,” F06. |
| `polyTimeComputable_blockMapFun` · 403 | Matches efficient polynomial-width block mapping. |
| `polyTimeComputable_preFun` · 422 | Matches efficient XOR preprocessing. |
| `polyTimeComputable_postFun` · 477 | Matches efficient query/verdict postprocessing. |
| `length_flatten_of_length` · 512 | Matches flattened length for equal chunks. |
| `length_maskOf` · 522 | Matches total message-vector mask length. |
| `decodeOracleMove_query` · 535 | Matches the canonical old query format. |
| `decodeOracleMove_ret` · 540 | Matches the old verdict format. |
| `postFun_layout` · 552 | Matches all branches of the composite layout. |
| `flatMap_ofFn` · 594 | Matches concatenation after mapping indexed blocks. |
| `preFun_encodeHist` · 602 | Matches the masked ciphertext encoding from canonical history. |
| `exists_queryChain_nuppt` · 629 | Gives evaluation agreement after a tape bijection, not exact query sequence; F06. |

### Asymptotic/PRF.lean

| Declaration | Statement versus docstring |
|---|---|
| `OracleEnsemble.random_O` · 142 | Matches identity evaluation of the random-table ensemble. |
| `OracleEnsemble.keyed_O` · 147 | Matches evaluation of the keyed family. |
| `acceptProb_random_eq_lazy` · 162 | Matches random-table/lazy-sampling acceptance for bounded adversaries. |
| `buildTree_boundedBy` · 218 | Matches the bound from every starting history, including zero budget. |
| `NUPPT.toOracleAdversary_boundedBy` · 242 | Matches the bound for every machine tape. |
| `OracleEnsemble.Indist.refl` · 263 | Matches reflexivity. |
| `OracleEnsemble.Indist.symm` · 274 | Matches symmetry. |
| `OracleEnsemble.Indist.trans` · 291 | Matches transitivity via negligible sums and triangle inequality. |
| `oracle_hybrid_lemma` · 314 | Matches an adjacent gap at least endpoint gap divided by positive hop count. |
| `prfAdv_toOracleAdversary` · 341 | Matches the ensemble/concrete advantage identity. |
| `PRF.negligible_prfAdv` · 350 | Matches negligible advantage for every machine and polynomial budget. |
| `DoublingPRG.negligible_prgAdv` · 383 | Matches negligible machine distinguishing advantage. |
| `two_mul_add_one_expands` · 395 | Matches strict expansion, including zero. |
| `PRG.doubling_apply` · 411 | Matches the iterate-and-last-bit output formula. |
| `PRG.Secure.truncate` · 429 | Matches secure truncation to `n+1` bits. |
| `PRG.Secure.doubling` · 449 | Matches secure length doubling. |
| `ggmPRF_apply` · 472 | Matches identification with `ggmBits`. |
| `exists_ggmPRF_evaluator` · 490 | Matches an efficient GGM evaluator from an efficient generator evaluator. |
| `thm_97_3_1` · 504 | Matches both hybrid endpoints with disclosed zero-based indexing. |
| `thm_97_3_2` · 520 | Matches the query-sub-hybrid sum bound under boundedness. |
| `decodeOracleMove_eq` · 536, private | Matches `queryOf`/`verdictOf`, including the sole accepting verdict. |
| `buildTree_eq_buildTreeQ` · 570, private | Matches the two builders at every budget and history. |
| `exists_ggmBitsDist_nuppt` · 619 | Matches concrete/machine advantage equality at in-range indices, not transcript identity. |
| `prfAdv_toOracleAdversary_zero` · 655, private | Matches zero advantage for zero queries against nonempty oracle distributions. |
| `ggmPRF_prf` · 694 | Matches GGM security under the doubling-PRG premise. |
| `exists_prf_of_exists_prg` · 751 | Matches PRF existence from PRG existence under the unchanged security notions. |

### Asymptotic/PRFLemmas.lean

| Declaration | Statement versus docstring |
|---|---|
| `take_ofFn_castLE` · 71 | Matches encoding of a bounded prefix. |
| `drop_take_ofFn_blocks` · 79 | Matches in-range fixed-width extraction. |
| `ofFn_prefixAt` · 97 | Matches the encoded prefix when its length is at most the input length. |
| `take_ofFn_splitHalves` · 108 | Matches the first half. |
| `drop_ofFn_splitHalves` · 115 | Matches the second half. |
| `selHalf_ofFn` · 129 | Matches the selected half under the reference-length assumption. |
| `length_selHalf_le` · 138 | Matches the unconditional reference-length bound. |
| `selHalf_poly` · 144 | Matches efficient selection from efficiently computed arguments. |
| `preFun_poly` · 163 | Matches efficient raw preprocessing. |
| `coins_preComp` · 178 | Matches exact coin-polynomial preservation. |
| `runAtL_preComp` · 182 | Matches the untyped activation equation. |
| `runAt_preComp` · 190 | Matches the typed activation equation. |
| `acceptProb_castLE` · 207 | Matches uniform-prefix preservation. |
| `PRG.Secure.truncateTo_easy` · 225 | Matches efficient evaluation after bounded polynomial truncation. |
| `PRG.Secure.truncateTo_negligible` · 248 | Matches negligible advantage after that truncation. |
| `ggmFrom_eq_walk` · 292 | Matches the suffix fold, including starting beyond the leaf depth. |
| `length_ggmStep_le` · 305 | Matches unconditional nonincrease of state length. |
| `length_ggmStep_iterate_le` · 322 | Matches the iterated length bound. |
| `ggmStep_poly` · 332 | Matches efficient guarded stepping. |
| `ggmStep_iterate` · 352 | Matches the label and remaining-bit state after the stated iterations. |
| `ggmEval_poly` · 382 | Matches efficient bounded-length iteration. |
| `ggmEval_ofFn_walk` · 391 | Matches the encoded walk from an n-bit label over arbitrary input bits. |
| `ggmEval_ofFn` · 402 | Matches the GGM value for correctly encoded key and input. |

### Foundations/Experiments.lean

| Declaration | Statement versus docstring |
|---|---|
| `invProb_def` · 87 | Matches the complete inversion-probability equation. |
| `predProb_def` · 91 | Matches the prediction-probability equation. |
| `acceptProb_def` · 95 | Matches the acceptance-probability equation. |
| `distAdv_def` · 99 | Matches the absolute acceptance gap. |
| `acceptProb_comp_equiv` · 104 | Matches bijective sampler-seed relabelling. |
| `uprob_comp_eq_sum_map` · 114 | Matches seed-event probability with pushforward mass. |
| `acceptProb_eq_uexp_sum_map` · 134 | Matches averaging acceptance-set mass over coins. |
| `abs_sum_sub_le_statDist` · 149 | Matches the total-variation bound on an event’s mass difference. |
| `distAdv_le_statDist` · 170 | Matches the randomized-distinguisher bound with explicit nonemptiness. |

### Foundations/Probability.lean

| Declaration | Statement versus docstring |
|---|---|
| `uexp_def` · 68 | Matches sum divided by finite cardinality. |
| `uprob_eq_card_filter` · 71 | Matches counting satisfying elements. |
| `uprob_eq_uexp` · 76 | Matches indicator expectation. |
| `uprob_nonneg` · 81 | Matches nonnegativity, including empty types. |
| `uprob_le_one` · 85 | Matches the upper bound, including empty types. |
| `uprob_true` · 91 | Matches normalization under necessary nonemptiness. |
| `uprob_false` · 97 | Matches zero probability. |
| `uprob_not` · 105 | Matches complement under necessary nonemptiness. |
| `uprob_mono` · 116 | Matches probability monotonicity under implication. |
| `uprob_or_le` · 123 | Matches the two-event union bound. |
| `uprob_exists_le` · 133 | Matches the finite indexed union bound. |
| `uprob_prod` · 149 | Matches product-space averaging. |
| `uprob_comp_equiv` · 161 | Matches bijective relabelling. |
| `uprob_fst` · 171 | Matches first projection with nonempty discarded factor. |
| `half_le_uprob_good` · 186 | Matches the averaging bound, including nonpositive threshold. |
| `abs_sub_le_sum_hybrids` · 214 | Matches the telescoping triangle bound. |
| `exists_hybrid_gap` · 226 | Matches an adjacent gap under positive hop count. |

### Games/BitCodec.lean

| Declaration | Statement versus docstring |
|---|---|
| `decodeIdx_replicate` · 64 | Matches the forward round trip; supplies neither converse nor malformed-index rejection. |
| `decodeBitMove_query` · 105 | Matches canonical query decoding, including zero-length payloads; does not characterize all accepted words. |
| `decodeBitMove_ret` · 112 | Matches correctly tagged exact-length returns. |

### Games/Bridges.lean

Import facade; no theorem declarations. Its contents list mentions T1 but should also mention T2. This is an editorial update, not another semantic finding.

### Games/Bridges/Experiments.lean

| Declaration | Statement versus docstring |
|---|---|
| `prob_sample_eq_uprob` · 65 | Matches on nonempty finite types; does not normalize the old empty-space convention. |
| `expect_sample_pair` · 72 | Matches sequential-independent/product sampling for every real test. |
| `prob_sample_pair` · 81 | Matches the corresponding event identity. |
| `invProb_eq` · 89 | Matches finding any preimage with independent instance and adversary seeds. |
| `predProb_eq` · 98 | Matches predicting the designated bit from the image and independent coins. |
| `acceptProb_eq` · 113 | Matches concrete acceptance with probability of game output true. |
| `distAdv_eq` · 124 | Matches the absolute gap with framework advantage. |

### Games/Bridges/Machines.lean

| Declaration | Statement versus docstring |
|---|---|
| `encodeLog_singleCodec` · 59 | Matches preservation of complete history encoding. |
| `buildComp_singleCodec` · 71 | Matches builders at every budget and starting history. |
| `toComp_singleCodec` · 95 | Matches decoders on the same parameter, budget, and tape; a proved equality, not the proposed defining equation. |

### Games/Bridges/QueryTree.lean

| Declaration | Statement versus docstring |
|---|---|
| `simulate_ofComp_pure` · 71 | Matches deterministic evaluation with unchanged state. |
| `eval_eq_evalFn` · 83 | Matches concrete/framework evaluation against deterministic oracles. |
| `simulate_eq` · 99 | Matches relabelling and answer conversion after discarding state. |
| `costBoundedBy_iff_boundedBy` · 112 | Matches old path bounds with unit-cost framework bounds, including zero. |

### Games/Bridges/Strategies.lean

| Declaration | Statement versus docstring |
|---|---|
| `turnParty_succ` · 88 | Matches sending the current value and installing the waiting continuation. |
| `alt_succ_last` · 105 | Matches the parity-selected receiver of the extra final message. |
| `exec_turnParty` · 133 | Matches outputs on final alternating histories with equal schedule/fuel and arbitrary initial histories. |
| `exec_eq_alt` · 154 | Matches D8 transcripts with front-recursive alternation and role swap. Its proof uses `alt_succ_last` and induction, unlike the prose’s `j+k` sketch. |
| `exec_strategies` · 173 | Matches fixed-tape outputs against `outP/outV` in the appropriate order, not view-distribution equivalence. |

### Games/Efficiency.lean

| Declaration | Statement versus docstring |
|---|---|
| `exists_handlerMachine` · 131 | Matches normalized non-uniform machine output with a seed/tape bijection and existential final state. Admitted; no exact raw length, adversary input, uniformity, or exposed state is asserted. |
| `exists_interactiveHandlerMachine` · 218 | Matches output-projected tree equality and product outer budget, with a bijection independent of `z`. Admitted; per-call budget counts queries, not activations. |

### Games/Hopping.lean

| Declaration | Statement versus docstring |
|---|---|
| `prob_split` · 72 | Matches partition into good and bad parts. |
| `expect_mono_of_allOutputs` · 82 | Matches expectation monotonicity on reachable outputs. |
| `prob_eq_one_of_allOutputs` · 91 | Matches probability one for a pathwise invariant under normalized sampling. |
| `prob_eq_zero_of_allOutputs` · 100 | Matches zero probability for excluded reachable outputs. |
| `abs_prob_sub_le_of_agree` · 111 | Matches the bad-event difference bound within one computation. |
| `prob_mem_le` · 138 | Matches a fresh uniform sample hitting an adaptively produced list under a pathwise length bound. |
| `simulate_allOutputs_bad` · 163 | Matches persistence of sticky bad state through simulation. |
| `expect_ite_one_split` · 174, private | Matches bad mass plus good-state expectation decomposition. |
| `prob_eq_until_bad` · 200 | Matches good-output and total bad-state mass equalities under agreement and stickiness. |
| `identical_until_bad` · 281 | Matches the difference bound using the first simulation’s final bad probability. |
| `hagree_of_eq` · 306 | Matches good-successor law equality from handler equality on good states. |
| `identical_until_bad_init` · 318 | Matches sampled initialization with all reachable initial states good. |

### Games/Machines.lean

| Declaration | Statement versus docstring |
|---|---|
| `buildComp_costBoundedBy` · 107 | Matches unit query cost bounded by fuel from every history; final inspection is not a query. |
| `NUPPT.toComp_costBoundedBy` · 127 | Matches the query bound on every tape. |
| `NUPPT.toCompOn_costBoundedBy` · 141 | Matches the same bound for every explicit input, without length restriction. |

### Games/OracleComp.lean

| Declaration | Statement versus docstring |
|---|---|
| `bind_eq_bind` · 102 | Matches monadic bind with structural bind. |
| `pure_eq_pure` · 106 | Matches monadic pure with the return constructor. |
| `map_eq_bind` · 109 | Matches mapping as bind-to-return. |
| `pure_bind` · 113 | Matches left identity. |
| `query_bind` · 117 | Matches sequencing through query continuations. |
| `bind_pure` · 122 | Matches right identity. |
| `bind_assoc` · 128 | Matches associativity. |
| `call_bind` · 146 | Matches a call followed by its continuation with a query node. |
| `liftLeft_bind` · 180 | Matches left embedding commuting with bind. |
| `liftRight_bind` · 188 | Matches right embedding commuting with bind. |
| `costBoundedBy_pure` · 208 | Matches every natural budget at a return. |
| `costBoundedBy_query` · 214 | Matches current cost fitting and all continuations fitting the remainder. |
| `CostBoundedBy.mono` · 221 | Matches budget monotonicity. |
| `CostBoundedBy.bind` · 235 | Matches additive sequential bounds. |
| `costBoundedBy_liftLeft` · 248 | Matches lifting with restricted union cost. |
| `costBoundedBy_liftRight` · 257 | Matches the corresponding right restriction. |
| `allOutputs_true` · 273 | Matches the universally true output invariant. |
| `AllOutputs.mono` · 280 | Matches transferring an invariant by implication. |
| `AllOutputs.bind` · 288 | Matches composing first-stage and continuation invariants. |

### Games/Protocols.lean

| Declaration | Statement versus docstring |
|---|---|
| `exec_zero` · 158 | Matches all zero-fuel branches, including closure and illegal sends. |
| `exec_succ` · 164 | Matches one delivered-message step with role exchange and outcome swap. |
| `endWithT_ne_outOfFuel` · 235 | Matches closure yielding completion or illegal send, never fuel exhaustion. |
| `execT_trace` · 251 | Matches total-count, alternation, and exact-exhaustion invariants pathwise. |
| `stepT_fst` · 280 | Matches projection to untraced stepping. |
| `closeT_fst` · 293 | Matches projection to untraced closure. |
| `endWithT_fst` · 306 | Matches projection to untraced ending. |
| `execT_outcome` · 318 | Matches the ordinary executor after projecting traced outcome. |

### Pseudorandom/Functions/Defs.lean

| Declaration | Statement versus docstring |
|---|---|
| `prfAdv_eq` · 74 | Matches the uniform-key/uniform-table absolute gap. |
| `prfAdv_nonneg` · 80 | Matches nonnegativity. |
| `acceptProb_congr` · 86 | Matches seedwise sampler equality preserving acceptance. |

### Pseudorandom/Functions/GGM.lean

| Declaration | Statement versus docstring |
|---|---|
| `ggmFrom_of_lt` · 85 | Matches one expansion/selection below leaf depth. |
| `ggmFrom_of_le` · 90 | Matches immediate return at or beyond leaf depth. |
| `hybridProb_zero` · 118 | Matches the uniform-root endpoint. |
| `hybridProb_top` · 127 | Matches the random-function endpoint. |
| `hybridProb_eq_level_prg` · 144 | Matches level simulation against generated label pairs. |
| `hybridProb_eq_level_random` · 163 | Matches next-level simulation against uniform pairs. |
| `hybridProb_level` · 211 | Matches the adjacent-level sum bound. |
| `ggm_prfAdv_le` · 231 | Matches the double sum over levels and challenges. |
| `exists_ggm_dist` · 246 | Matches averaging with both index sets nonempty. |
| `distAdv_ggmBitsDist` · 303 | Matches advantage preservation through split halves. |
| `ggmBits_prfAdv_le` · 321 | Matches the bit-string double-sum bound. |
| `exists_ggmBits_dist` · 331 | Matches the existential bound with positive depth and budget. |

### Pseudorandom/Functions/LazySampling.lean

| Declaration | Statement versus docstring |
|---|---|
| `uprob_congr` · 59 | Matches pointwise event equivalence. |
| `uprob_prod_comm` · 63 | Matches exchanging product coordinates. |
| `uprob_snd` · 69 | Matches second projection with nonempty discarded factor. |
| `uprob_sections_congr` · 76 | Matches product equality from section equalities. |
| `uprob_update_absorb` · 86 | Matches fresh uniform replacement of one table entry with extra coins retained. |
| `uprob_update_absorb'` · 99 | Matches replacement without extra coins. |
| `uprob_update_split` · 111 | Matches exposing an ignored table entry as fresh randomness. |
| `noteQuery_of_mem` · 129 | Matches retaining history on a repeated query. |
| `noteQuery_of_not_mem` · 132 | Matches appending a new query. |
| `idxOf_noteQuery_lt` · 136 | Matches the query’s position lying in updated history. |
| `length_noteQuery_le` · 142 | Matches length increase by at most one. |
| `evalLazy_ret` · 156 | Matches the leaf equation. |
| `evalLazy_query` · 160 | Matches first-occurrence stream selection. |
| `evalLazy_congr` · 166 | Matches dependence only below initial-history length plus budget. |
| `evalLazy_comp` · 182 | Matches answer postprocessing with simulation conversion. |
| `uprob_const_eq` · 201, private | Matches constant events on two nonempty sample spaces. |
| `extendStream_update_of_ne` · 225 | Matches invariance away from an updated entry, including fallback positions. |
| `extendStream_update_self` · 233 | Matches the new value at the entry. |
| `extendStream_combine_of_lt` · 237, private | No docstring; preserves the prefix below the splice, including fallback positions. |
| `extendStream_combine_self` · 242, private | No docstring; reads the fresh entry at an in-range splice. |
| `combine_succ` · 247, private | No docstring; moves one fresh entry into the fixed prefix without changing the combined stream. |
| `combine_update` · 261, private | No docstring; ignores fresh-coordinate changes covered by the fixed prefix. |
| `mergeTable_append` · 270, private | No docstring; recording a new query with its old value preserves the merged oracle. |
| `mergeTable_update` · 287, private | No docstring; ignores random-table changes overridden by history. |
| `uprob_evalLazy_aux` · 313, private | Matches the conditional-history invariant with its explicit length-plus-budget bound; no hidden distinctness premise is needed. |
| `uprob_evalLazy` · 379 | Matches output-event equality between bounded lazy sampling and a uniform function table. |

### Pseudorandom/Functions/OracleAdversary.lean

| Declaration | Statement versus docstring |
|---|---|
| `eval_ret` · 108 | Matches leaf evaluation after restatement. |
| `eval_query` · 111 | Matches the branch selected by the answer. |
| `boundedBy_ret` · 123 | Matches every budget at leaves. |
| `boundedBy_query_zero` · 127 | Matches rejection of queries at zero, even with empty answer type. |
| `boundedBy_query_succ` · 132 | Matches the positive-budget recursive characterization. |
| `BoundedBy.mono` · 136 | Matches increasing the budget. |
| `eval_simulate` · 156 | Matches evaluation after query relabelling/answer conversion. |
| `BoundedBy.simulate` · 164 | Matches preservation under one-query-per-query simulation. |

### Pseudorandom/Functions/SubHybrids.lean

| Declaration | Statement versus docstring |
|---|---|
| `acceptProb_tableDist_prg` · 118 | Matches a generated challenge with sub-hybrid `j`, for `j<q`. |
| `acceptProb_tableDist_uniform` · 155 | Matches a uniform challenge with sub-hybrid `j+1`, for `j<q`. |
| `subHybridProb_zero` · 204 | Matches the generated-table endpoint with boundedness. |
| `subHybridProb_top` · 238 | Matches the random-table endpoint with boundedness. |
| `table_hybrid` · 268 | Matches the sum of adjacent distinguishing gaps bounding endpoints. |

### Games/Probability.lean — supplied context

| Declaration | Statement versus docstring |
|---|---|
| `expect_pure` · 101 | Matches testing the returned value. |
| `expect_query` · 104 | Matches uniform averaging over sampling answers. |
| `expect_bind` · 112 | Matches total expectation. |
| `expect_map` · 119 | Matches composition of the test with the output map. |
| `expect_sampleFin` · 124 | Matches uniform averaging over a nonempty finite range. |
| `expect_sample` · 131 | Matches uniform averaging over a nonempty finite type. |
| `expect_add` · 142 | Matches additivity. |
| `expect_const_mul` · 149 | Matches multiplication by any real constant. |
| `expect_const` · 158 | Matches normalization. |
| `expect_sum` · 168 | Matches finite-sum interchange. |
| `expect_mono` · 177 | Matches pointwise monotonicity. |
| `expect_nonneg` · 186 | Matches nonnegative tests. |
| `prob_eq_expect` · 192 | Matches indicator expectation with any decidability instance. |
| `prob_pure` · 200 | Matches the returned-value indicator. |
| `prob_bind` · 208 | Matches total probability. |
| `prob_nonneg` · 214 | Matches nonnegativity. |
| `prob_le_one` · 220 | Matches the upper bound one. |
| `prob_mono` · 228 | Matches implication monotonicity. |
| `prob_congr` · 238 | Matches pointwise event equivalence. |
| `prob_or_le` · 243 | Matches the two-event union bound. |
| `prob_not` · 251 | Matches normalized complement. |
| `dist_apply` · 275 | Matches the output distribution’s point mass. |

### Games/Simulate.lean — supplied context

| Declaration | Statement versus docstring |
|---|---|
| `simulate_pure` · 84 | Matches return with unchanged state. |
| `simulate_query` · 88 | Matches a handler call followed by state-threaded continuation. |
| `simulate_bind` · 98 | Matches state-threaded sequencing. |
| `simulate_call` · 105 | Matches a simulated single call with the handler. |
| `simulate_comp` · 152 | Matches implementation composition with state reassociation. |
| `simulate_withLog` · 185 | Matches plain simulation after forgetting the added log. |
| `simulate_costBoundedBy` · 208 | Matches source budgets measured through per-query target costs. |

### Games/Advantage.lean — supplied context

| Declaration | Statement versus docstring |
|---|---|
| `accept_nonneg` · 70 | Matches nonnegative acceptance probability. |
| `accept_le_one` · 73 | Matches the upper bound one. |
| `advantage_nonneg` · 76 | Matches nonnegative absolute gap. |
| `advantage_comm` · 79 | Matches symmetry. |
| `advantage_self` · 83 | Matches zero self-gap. |
| `advantage_le_one` · 86 | Matches the upper bound one for normalized games. |
| `advantage_triangle` · 93 | Matches the intermediate-game triangle bound. |
| `advantage_hybrid` · 101 | Matches the finite-chain sum bound. |
| `exists_advantage_hybrid_gap` · 112 | Matches an adjacent gap under positive hop count, with the sharper source convention disclosed. |
| `accept_guessGame` · 132 | Matches averaging correct guesses over equally likely branches. |
| `guessAdv_eq_half_advantage` · 162 | Matches the exact factor-of-two relation between guessing bias and distinguishing advantage. |

## Source alignment and supplemental dependencies

The framework provides implementation/proof interfaces; it is not itself a new MAC, signature, encryption, or two-party security definition.

Source checks covered:

- Probabilistic and non-uniform machine conventions: book pp. 23–26.
- Random functions and PRFs: pp. 95–99.
- Inherited multi-message hybrids: pp. 99–100.
- Interaction and full-view conventions: pp. 115–116 and 155–156.
- Cited authentication and composability reductions: pp. 134–136, 144, 168–170, and 175.

D8’s declared scheduling/output convention was distinguished from the broader coroutine executor.

Pinned supplemental sources:

- [NUPPT](https://github.com/Shilun-Allan-Li/tcslib/blob/afe5982f612081bba2fbcec9ab41adcbbc118b13/TCSlib/Complexity/Randomized/PPT.lean#L125)
- [Pairing and parsing](https://github.com/Shilun-Allan-Li/tcslib/blob/afe5982f612081bba2fbcec9ab41adcbbc118b13/TCSlib/Complexity/TuringMachine/Encoding.lean)
- [Fixed-length decoding and padFin](https://github.com/Shilun-Allan-Li/tcslib/blob/afe5982f612081bba2fbcec9ab41adcbbc118b13/TCSlib/Cryptography/Asymptotic/Adversary.lean#L77)
- [D8 strategies, transcripts, outputs, and views](https://github.com/Shilun-Allan-Li/tcslib/blob/afe5982f612081bba2fbcec9ab41adcbbc118b13/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean)

No preservation claim depends on the changing default branch. This report does not certify future view bridges, protocol-efficiency theorems, or admitted efficiency fills.

## Notation glossary

- `T`: recursive transport from pre-F1 query trees to one-oracle computations.
- `U`: its recursive inverse.
- `old`, `new`: pre-F1 and audited-head versions.
- `r_P`, `r_V`: fixed prover/verifier tapes, encoded as lists when supplied to `Strategy.next`.
- `1^i`: `List.replicate i true`.
- Other identifiers are the audited Lean declarations and parameters described above.