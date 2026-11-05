## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/pack-r2.md =====

# Gate 04 (Pass–shelat ch. 5–8, S2b), round 2: external closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
(`cryptography/pass-shelat-ch5-8-s2b` into `cryptography/pass-shelat-ch2-4`) at its head
`243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`.
- **Round 1** audited `afe5982f612081bba2fbcec9ab41adcbbc118b13` and found **0 blockers, 2 majors,
  4 minors** (`gate04-s2b-findings.md`, in the bundle, verbatim). The maintainer's review added N1
  (proposed major: T1/T2 do not cover the reductions they are cited for) and N2–N7 (minor).
- **The repairs:** two commits after `afe5982f`: `f6d57307` (F01–F04, F06, N5, N6) and `243598b7`
  (N1, ruling R-04-3). Their full diff is `evidence-r2/repair.diff.txt`; each item's resolution is
  in `resolutions-r1.md` (both in the bundle).
- **The deliverable:** **`gate04-s2b-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each of F01–F06 and N1–N7 say whether the resolution
   is adequate: **fixed** (the defect is gone, and the fix introduces no new one), **recorded**
   (accepted as declared or scheduled work, and the record is accurate), or **not resolved** (say
   why).
2. **It audits the changed surface afresh:**
   - the codec: is `decodeIdx` now exact, and do the converse lemmas characterize `decodeBitMove`
     on every word?
   - the equation lemmas: does each state its definition's defining equation (and nothing
     stronger or weaker)? Do the re-pointed proofs avoid reading other files' definitions?
   - **the efficiency layer, restated (R-04-3):** `seedIn`; the new handler fields (`advIn`,
     `out`; `outLen`, `finCall`, `finRun`); T1 with exact output; T2 with the finalization and
     budget `q·perCall + finCall`; the companion `exists_toCompOn_of_toComp`; T4
     `exists_toOracleAdversary_of_bitCodec`. Restate each new or changed definition in your own
     words before reading its docstring, and say whether each statement is what its docstring
     claims. Are T1, T2 and T4 **usable contracts** for the reductions listed in the resolutions'
     table (one adversary run, polynomial input and finalization, exact output)? Is any hypothesis
     missing or vacuous?

Attempt at least **three adversarial instantiations** of the new handlers. Look for regressions:
anything round 1 accepted that the repairs broke. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 1 findings, resolutions, repair diff | `gate04-s2b-findings.md`, `resolutions-r1.md`, `evidence-r2/repair.diff.txt` |
| Changed Lean, at `243598b7` | the 25 files of `evidence-r2/changed-files.txt` (S2b's files, S2a's `Advantage`, `Simulate`, `OracleComp`, `Protocols`, and ch. 2–4's `Interaction`, which gained equation lemmas) |
| Context | `policy.md`; `design/S2b-efficiency.md` (stale on the efficiency layer's statements: superseded by R-04-3, see the resolutions) |

## Attestations (maintainer execution claims; `evidence-r2/`)

- **Elaboration** (`replay.log`): the 60 modules downstream of the files changed since `afe5982f`,
  in import order, from a fresh copy of the `afe5982f` olean tree: **all pass, 0 errors**.
  `sorry` warnings only in `Games/Efficiency` (4: T1, T2, the companion, T4) and the
  pre-existing 3-colouring stubs (3).
- **Axioms** (`axioms.log`): every public theorem of the 25 changed files, 379; **375 standard**;
  `sorryAx` exactly in T1, T2, `exists_toCompOn_of_toComp` and T4.
- **Lint** (`lint.log`): 0 findings in each of the 25 files. **Check 8** (`check8.log`, N2/N7):
  0 failures in `Games/`; 3 warnings on older S2a definitions. The **rule-10 seal** check (each
  re-pointed consumer compiled with the other files' definitions `local irreducible`) was run by
  the repair worker (script `seal.py.txt`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 item: `F01: fixed / recorded / not resolved — <reason>` (also N1–N7).

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major** (fixable
but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge case,
naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== gate04-s2b-findings.md =====

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

## ===== resolutions-r1.md =====

# Gate 04 (S2b, #195): round 1 resolutions

- **Round 1:** findings `findings/gate04-s2b-findings.md`, verbatim, SHA-256
  `24949274f226fb42bc5ea4d69e39feb50e7c4bee5e3aec56c04d0a9625054246`; head
  `afe5982f612081bba2fbcec9ab41adcbbc118b13`. Counts: **0 blockers, 2 majors (F01, F02), 4 minors
  (F03–F06).**
- **Review:** `review/gate04-review.md`: all six true, severities agreed. It adds N1 (proposed major:
  T1/T2 do not cover the reductions they are cited for) and N2–N7 (minor).
- **Rulings (user, 2026-11-05):** R-04-1 strict unary decoding with converses; R-04-2 every
  equation lemma S2b's proofs consume, in #195 (S2b's, S2a's and ch. 2–4's `Interaction.lean`);
  R-04-3 extend T0–T2 before the efficiency fill.
- **Repairs:** two commits on #195's branch after `afe5982f`:
  - `f6d573075e6e71f00d3f8e29a8285a585482d589`: F01–F04, F06, N5, N6 (19 files, +832/−78);
  - `243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`: R-04-3 (N1) (`Games/Efficiency.lean`, the
    `Games/Bridges.lean` facade).

| Item | Severity | Resolution |
|---|---|---|
| F01 | major | **Fixed** (R-04-1). `decodeIdx` requires `iw = List.replicate iw.length true`; `decodeIdx_replicate` re-proved; converses `decodeIdx_eq_some_iff`, `decodeIdx_eq_none_iff`, `decodeBitMove_eq_query_iff`, `decodeBitMove_of_not_canonical`; `encodeBitMove` with `decodeBitMove_encodeBitMove` and `encodeBitMove_injective`. No statement text changes; no notion changes meaning (every one quantifies over all adversaries). |
| F02 | major | **Fixed** (R-04-2). 91 public equation lemmas next to their definitions in 14 files (BitCodec 16, Protocols 10, Efficiency 9, Machines 8, PRF 7, `Interaction` 7, Simulate 6, Bridges/Machines 6, Bridges/Strategies 6, OracleAdversary 5, OracleComp 4, Advantage 3, Bridges/QueryTree 3, Bridges/Experiments 1); the 16 consumer proofs re-pointed, plus `Hopping.prob_eq_until_bad`. A rule-10 seal check (`attribute [local irreducible]` on other files' definitions) passes on the re-pointed files, and fails on the old versions. |
| F03 | minor | **Fixed.** `PolyHandler.answer`'s componentwise default and `InteractiveHandler`'s joint default stated (N6 folded in). |
| F04 | minor | **Fixed.** "at most `perCall(n)` outer queries, in at most `perCall(n) + 1` rounds". |
| F05 | minor | **Fixed at staging:** the evidence is regenerated at the new head (`evidence-r2/`). The round 1 attestation should have read 237 public theorems, 235 standard and T1/T2 with `sorryAx`; the 14 private theorems are covered by the replay. |
| F06 | minor | **Fixed.** Six docstrings made to match their statements (`multiMsgAdv_boundedBy`, `decodeFin_runAt_prfDec_of_not_wf`, `pairFstD_pairFstD_histBlock`, `take_drop_ofFn_blocks`, `exists_queryChain_nuppt`, `tableDist`/`ggmDist`). |
| N1 | major (proposed) | **Fixed** (R-04-3). `seedIn` (the context `⟨1^n, ⟨z, ω⟩⟩`); `PolyHandler` gains `advIn` and `out`, `InteractiveHandler` gains `advIn`, `outLen`, `finCall` and `finRun`, each with equation lemmas. T1 restated with exact output; T2 with the finalization and budget `q·perCall + finCall`; the companion `exists_toCompOn_of_toComp` and T4 `exists_toOracleAdversary_of_bitCodec` stated. All four are `sorry` (the fill's targets). The eight prong sketches are re-cited at integration (table below). |
| N2 | minor | **Fixed at staging:** check 8 and the seal evidence are in `evidence-r2/`. |
| N3 | minor | **Recorded:** `Bridges/Strategies.lean`'s promise of later results is reworded at integration with the prongs that supply them. |
| N4 | minor | **Recorded:** `take_drop_ofFn_blocks` is ledgered with the `blocks` family (G3-5; DL-9 onward), paid back in the ch. 2–4 clean-up PR. |
| N5 | minor | **Fixed.** `Option.elim_none`/`_some` replace `simp [Option.elim]`. |
| N6 | minor | **Fixed** with F03. |
| N7 | minor | **Fixed at staging** with N2. |

**Prerequisites recorded for the efficiency fill** (rule 10; ch. 2–4 clean-up PR): `NUPPT.coinLen_eq`
beside `coinLen` (`Complexity/Randomized/PPT.lean`), and `decodeOracleMove`'s case lemmas beside its
definition.

**The eight prong sketches to re-cite** (docstrings only; no statement changes):

| Site | Must cite |
|---|---|
| Thm 135.4, prong A `PRFMAC.lean` | the companion (input-free forger), then **T2** (forwarding handler; `finish` with `finCall = 1`: query at `m`, freshness from the state; `outLen = 1`; budget `q + 1`), then **T4** to reach `OracleEnsemble.Indist` |
| Thm 137.2, `Lamport.lean` | **T1**: `advIn` builds `pk` from `y = z` and the seed; answer or abort; `out` returns `σ'_i` |
| Thm 144.1 `B`, `HashAndSign.lean` | **T1**: `advIn = ⟨pk, i⟩`; `out = (m, m′)` |
| Thm 144.1 `C`, `HashAndSign.lean` | **T2**: `advIn = ⟨pk, i⟩`; queries forwarded as `h_i(m)` (`perCall = 1`); `finish` with `finCall = 0` |
| Thm 168.2, prong C `PRFScheme.lean` | **T2** (Enc and the challenge by oracle queries; `b` in the seed; `finish` compares the guess with `b`) + **T4** (+ the companion) |
| Thm 170.4, `CCA2Scheme.lean` | **T2** (`Enc′`/`Dec′` through the oracle; `k₁` in the seed) + **T4** (+ the companion), lengths `2n` |
| Thm 175.9 (⇒), `NonMalleable.lean` | **T2**: `advIn = pk`; `Dec` forwarded; `finish` with `finCall = ℓ` then `D` (advice through `z`; `exists_withAdvice`/`exists_comp`); budget `q + ℓ` |
| `padded_cpa`, `PublicKey.lean` | **T1**: `advIn = pk` from `z = ⟨pk, c⟩`; the challenge answered with `padCt L c`; `out` flips or zeroes the bit |

## ===== evidence-r2/repair.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/MultiMessage.lean b/TCSlib/Cryptography/Asymptotic/MultiMessage.lean
index 394fd28b..e8cde0a8 100644
--- a/TCSlib/Cryptography/Asymptotic/MultiMessage.lean
+++ b/TCSlib/Cryptography/Asymptotic/MultiMessage.lean
@@ -144,7 +144,7 @@ def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
   fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2
 
 omit [Fintype ρ] in
-/-- `multiMsgAdv m D` makes exactly `q + 1` queries. -/
+/-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
 theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
     (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
     (multiMsgAdv m D).BoundedBy (q + 1) :=
@@ -464,8 +464,8 @@ theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (
   rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
   simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
 
-/-- On a ciphertext `w` that is not a pair of `n`-bit strings, the decryption machine outputs
-`⊥`: a string that decodes to no `n`-bit message. -/
+/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
+long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
 theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
     (coins : PolyExpr) (n : ℕ) (k w : List Bool)
     (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
diff --git a/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean b/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
index afc7b269..c89380bc 100644
--- a/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
@@ -296,7 +296,8 @@ theorem flatMap_const_replicate {α : Type*} (n : ℕ) : ∀ L : List α,
     rw [List.flatMap_cons, flatMap_const_replicate n L, List.length_cons, Nat.succ_mul, add_comm,
       List.replicate_add]
 
-/-- The two components of a history block: the query and the answer. -/
+/-- The query component of a history block: `pairFstD (pairFstD (histBlock p))` is the query
+`p.1`. -/
 theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
     pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
   simp [histBlock]
@@ -375,7 +376,8 @@ theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
       zipWith_xor_flatten_ofFn (fun j => F j.succ) (fun j => G j.succ) fun j => h j.succ]
 
 /-- A string of `q·s` bits read as `q` chunks of `s` bits: chunk `i` is block `i` of
-`FunFamily.blocks` (private copy of the lemma of `Asymptotic/EnsemblesLemmas.lean`). -/
+`FunFamily.blocks` (a public duplicate of `EnsembleLemmas.take_drop_ofFn_blocks` in
+`Asymptotic/EnsemblesLemmas.lean`). -/
 theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
     ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) := by
   have hle : i * s + s ≤ q * s := by
@@ -616,8 +618,9 @@ by closure under efficient operations we contradict the pseudorandomness propert
 non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
 message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
 are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
-query tree with budget `q(n) + 1` run against any oracle `g` asks `ρ₀, …, ρ_{q(n)}` and
-outputs `D`'s verdict on the encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c`.
+query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
+encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
+queries is not part of the statement).
 
 **Proof sketch.** `B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of
 `exists_withAdvice` (advice `⟨maskOf (v n), 1^{q(n)+1}⟩`) of `exists_seq` of `D ∘ preFun`
diff --git a/TCSlib/Cryptography/Asymptotic/PRF.lean b/TCSlib/Cryptography/Asymptotic/PRF.lean
index c36beb40..d305cd99 100644
--- a/TCSlib/Cryptography/Asymptotic/PRF.lean
+++ b/TCSlib/Cryptography/Asymptotic/PRF.lean
@@ -201,6 +201,18 @@ nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
 def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
   h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []
 
+/-- The empty history is encoded as the empty string: `encodeHist [] = []`. -/
+theorem encodeHist_nil {ℓ₁ ℓ₂ : ℕ} :
+    encodeHist ([] : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) = [] :=
+  rfl
+
+/-- A history is encoded pair by pair:
+`encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h)`. -/
+theorem encodeHist_cons {ℓ₁ ℓ₂ : ℕ} (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))
+    (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
+    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
+  rfl
+
 /-- The query tree of a next-query function `next` (the machine's move on a history) with the
 query budget `q`, started from the history `hist`: a verdict stops; a query within budget
 becomes a `query` node whose continuation appends the answer to the history; a query when the
@@ -214,6 +226,38 @@ def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin
     | .ret b => .ret b
     | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))
 
+section BuildTree
+
+variable {ℓ₁ ℓ₂ : ℕ} {next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁}
+  {hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))}
+
+/-- With the budget spent, a verdict stops the tree: `buildTree next 0 hist = ret b` when
+`next hist = ret b`. -/
+theorem buildTree_zero_of_ret {b : Bool} (h : next hist = .ret b) :
+    buildTree next 0 hist = .ret b := by
+  rw [buildTree, h]
+
+/-- With the budget spent, a query gives the forced verdict `false`:
+`buildTree next 0 hist = ret false` when `next hist = query x`. -/
+theorem buildTree_zero_of_query {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
+    buildTree next 0 hist = .ret false := by
+  rw [buildTree, h]
+
+/-- Within budget, a verdict stops the tree: `buildTree next (q + 1) hist = ret b` when
+`next hist = ret b`. -/
+theorem buildTree_succ_of_ret {q : ℕ} {b : Bool} (h : next hist = .ret b) :
+    buildTree next (q + 1) hist = .ret b := by
+  rw [buildTree, h]
+
+/-- Within budget, a query becomes a query node whose continuation appends the answer:
+`buildTree next (q + 1) hist = query x (fun o => buildTree next q (hist ++ [(x, o)]))` when
+`next hist = query x`. -/
+theorem buildTree_succ_of_query {q : ℕ} {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
+    buildTree next (q + 1) hist = .query x (fun o => buildTree next q (hist ++ [(x, o)])) := by
+  rw [buildTree, h]
+
+end BuildTree
+
 /-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
 theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
     (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
@@ -236,6 +280,16 @@ def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : 
     OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
   fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []
 
+/-- The tree of `D` on the coins `r` is built from the empty history, the next move being `D`'s
+output on the encoded history, decoded:
+`D.toOracleAdversary n ℓ₁ ℓ₂ q r =
+buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []`. -/
+theorem _root_.Complexity.NUPPT.toOracleAdversary_eq (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ)
+    (r : D.Coins n) :
+    D.toOracleAdversary n ℓ₁ ℓ₂ q r =
+      buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q [] :=
+  rfl
+
 /-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
 every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
 Induction on the budget (`buildTree_boundedBy`). -/
diff --git a/TCSlib/Cryptography/Games/Advantage.lean b/TCSlib/Cryptography/Games/Advantage.lean
index 79d2107f..1012c334 100644
--- a/TCSlib/Cryptography/Games/Advantage.lean
+++ b/TCSlib/Cryptography/Games/Advantage.lean
@@ -62,10 +62,20 @@ open Finset ProbComp
 /-- The probability that the game `G` outputs `true`. -/
 noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)
 
+/-- The acceptance probability is the probability of the output `true`:
+`accept G = prob G (· = true)`. -/
+theorem accept_eq (G : ProbComp Bool) : accept G = prob G (· = true) :=
+  rfl
+
 /-- The **distinguishing advantage** between two games: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
 [PS10, §3.1] -/
 noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|
 
+/-- The distinguishing advantage is the absolute gap of the acceptance probabilities:
+`advantage G₀ G₁ = |accept G₀ - accept G₁|`. -/
+theorem advantage_eq (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = |accept G₀ - accept G₁| :=
+  rfl
+
 /-- An acceptance probability is nonnegative. -/
 theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _
 
@@ -121,6 +131,12 @@ is `b`: the prediction experiment `b ← {0,1}; t ← X^b : A(t) = b` of [PS10,
 noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
   (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))
 
+/-- The guess-the-bit game samples `b`, runs `G b` and outputs whether it returned `b`:
+`guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))`. -/
+theorem guessGame_eq (G : Bool → ProbComp Bool) :
+    guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b)) :=
+  rfl
+
 /-- The **guess-the-bit advantage**: how far the winning probability is from `½`. -/
 noncomputable def guessAdv (G : Bool → ProbComp Bool) : ℝ := |accept (guessGame G) - 1 / 2|
 
diff --git a/TCSlib/Cryptography/Games/BitCodec.lean b/TCSlib/Cryptography/Games/BitCodec.lean
index 884cf73b..2e89dc94 100644
--- a/TCSlib/Cryptography/Games/BitCodec.lean
+++ b/TCSlib/Cryptography/Games/BitCodec.lean
@@ -32,12 +32,16 @@ It is the shared codec of every prong's statements, and the T0 definitions of th
 * `Games.bitSpec din dout`: `k` oracles on fixed-length bit strings.
 * `Games.decodeIdx`, `Games.decodeBitMove`: decoding of an oracle index and of a machine output as
   a move.
+* `Games.encodeBitMove`: the canonical word of a move.
 * `Games.bitCodec din dout dα`: the codec.
 
 ## Main results
 
 * `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
   well-formed encodings decode as intended.
+* `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
+  decode as an index or a query.
+* `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
 
 ## References
 
@@ -56,20 +60,67 @@ variable {k : ℕ}
 abbrev bitSpec (din dout : Fin k → ℕ) : OracleSpec (Fin k) :=
   ⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩
 
-/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`. -/
+/-- Oracle `i` of `bitSpec din dout` takes `din i`-bit strings. -/
+theorem bitSpec_dom (din dout : Fin k → ℕ) (i : Fin k) :
+    (bitSpec din dout).dom i = (Fin (din i) → Bool) :=
+  rfl
+
+/-- Oracle `i` of `bitSpec din dout` answers with `dout i`-bit strings. -/
+theorem bitSpec_rng (din dout : Fin k → ℕ) (i : Fin k) :
+    (bitSpec din dout).rng i = (Fin (dout i) → Bool) :=
+  rfl
+
+/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
+(one containing `false`, or of length at least `k`) is `none`. -/
 def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
-  if h : iw.length < k then some ⟨iw.length, h⟩ else none
+  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none
 
 /-- The unary code of an index decodes to it. -/
 theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
   unfold decodeIdx
-  have h : (List.replicate (i : ℕ) true).length < k := by simp
+  have h : (List.replicate (i : ℕ) true).length < k ∧
+      List.replicate (i : ℕ) true =
+        List.replicate (List.replicate (i : ℕ) true).length true := by
+    simp
   rw [dif_pos h]
   exact congrArg some (Fin.ext (by simp))
 
+/-- **Exactly the unary codes decode**, each to its index:
+`decodeIdx k iw = some i ↔ iw = 1^i`. -/
+theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
+    decodeIdx k iw = some i ↔ iw = List.replicate i true := by
+  refine ⟨fun h => ?_, fun h => h ▸ decodeIdx_replicate i⟩
+  unfold decodeIdx at h
+  split_ifs at h with hw
+  rw [Option.some.injEq] at h
+  rw [← h]
+  exact hw.2
+
+/-- **Every other word is rejected:** `decodeIdx k iw = none` exactly when `iw` is the unary code
+of no index below `k`. -/
+theorem decodeIdx_eq_none_iff {iw : List Bool} :
+    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true := by
+  constructor
+  · intro h i hi
+    rw [decodeIdx_eq_some_iff.2 hi] at h
+    exact Option.some_ne_none i h
+  · intro h
+    cases hd : decodeIdx k iw with
+    | none => rfl
+    | some i => exact absurd (decodeIdx_eq_some_iff.1 hd) (h i)
+
 /-- The default output: the all-`false` string. -/
 def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false
 
+/-- Every bit of the default output is `false`: `zeroBits d j = false`. -/
+theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
+  rfl
+
+/-- The default output, written as a string, is `d` copies of `false`:
+`List.ofFn (zeroBits d) = List.replicate d false`. -/
+theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
+  rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]
+
 /-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
 `⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
 `⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
@@ -92,6 +143,26 @@ def decodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
     | none => .ret (zeroBits dα)
   | _ => .ret (zeroBits dα)
 
+/-- **The canonical word of a move:** the query `x` to oracle `i` is `⟨[false], ⟨1^i, x⟩⟩`, and
+the output `a` is `⟨[true], a⟩`. `decodeBitMove` inverts it (`decodeBitMove_encodeBitMove`). -/
+def encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) :
+    Move (bitSpec din dout) (Fin dα → Bool) → List Bool
+  | .query i x => pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
+  | .ret a => pairEncode [true] (List.ofFn a)
+
+/-- The canonical word of a query:
+`encodeBitMove din dout dα (query i x) = ⟨[false], ⟨1^i, x⟩⟩`. -/
+theorem encodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
+    (x : Fin (din i) → Bool) :
+    encodeBitMove din dout dα (.query i x) =
+      pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
+  rfl
+
+/-- The canonical word of an output: `encodeBitMove din dout dα (ret a) = ⟨[true], a⟩`. -/
+theorem encodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
+    encodeBitMove din dout dα (.ret a) = pairEncode [true] (List.ofFn a) :=
+  rfl
+
 /-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
 `(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
 def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
@@ -101,6 +172,35 @@ def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
     pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
   timeout := zeroBits dα
 
+/-- The codec decodes moves with `decodeBitMove`: `(bitCodec din dout dα).decodeMove w =
+decodeBitMove din dout dα w`. -/
+theorem bitCodec_decodeMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
+    (bitCodec din dout dα).decodeMove w = decodeBitMove din dout dα w :=
+  rfl
+
+/-- The codec encodes the log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
+theorem bitCodec_encodeEntry (din dout : Fin k → ℕ) (dα : ℕ)
+    (e : Σ i, (bitSpec din dout).dom i × (bitSpec din dout).rng i) :
+    (bitCodec din dout dα).encodeEntry e =
+      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
+  rfl
+
+/-- When the budget runs out, the codec's output is all-`false`:
+`(bitCodec din dout dα).timeout = zeroBits dα`. -/
+theorem bitCodec_timeout (din dout : Fin k → ℕ) (dα : ℕ) :
+    (bitCodec din dout dα).timeout = zeroBits dα :=
+  rfl
+
+/-- The codec's log encoding does not depend on the output length: `bitCodec din dout dα` and
+`bitCodec din dout dα'` encode every log alike. -/
+theorem encodeLog_bitCodec (din dout : Fin k → ℕ) (dα dα' : ℕ) (h : QueryLog (bitSpec din dout)) :
+    (bitCodec din dout dα).encodeLog h = (bitCodec din dout dα').encodeLog h := by
+  induction h with
+  | nil => rw [MachineCodec.encodeLog_nil, MachineCodec.encodeLog_nil]
+  | cons e h ih =>
+    rw [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih, bitCodec_encodeEntry,
+      bitCodec_encodeEntry]
+
 /-- A well-formed query decodes as the query. -/
 theorem decodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
     (x : Fin (din i) → Bool) :
@@ -113,4 +213,96 @@ theorem decodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα 
     decodeBitMove din dout dα (pairEncode [true] (List.ofFn a)) = .ret a := by
   simp [decodeBitMove, pairDecode_pairEncode, decodeFin_ofFn]
 
+/-- A decoded `ℓ`-bit string is the string itself (read through `decodeFin`'s published lemmas
+only). -/
+private theorem eq_ofFn_of_decodeFin {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
+    (h : decodeFin ℓ w = some x) : w = List.ofFn x := by
+  have hw := length_eq_of_decodeFin_eq_some h
+  subst hw
+  have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
+  rw [List.ofFn_get, h, Option.some.injEq] at h'
+  rw [h']
+  exact (List.ofFn_get w).symm
+
+/-- **Only the canonical query word decodes as a query:** `decodeBitMove din dout dα w` is the
+query `x` to oracle `i` exactly when `w = ⟨[false], ⟨1^i, x⟩⟩` (the converse of
+`decodeBitMove_query`).
+
+**Proof sketch.** Follow `decodeBitMove`'s branches: only the branch in which the tag is `[false]`,
+the rest parses as a pair, the index word decodes and the payload has the right length returns a
+query. There, each successful parse determines its input: a parsed pair is the pairing of its parts
+(`eq_pairEncode_of_pairDecode`), a decoded index word is `1^i` (`decodeIdx_eq_some_iff`), and a
+decoded payload is `List.ofFn x`. -/
+theorem decodeBitMove_eq_query_iff {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool} {i : Fin k}
+    {x : Fin (din i) → Bool} :
+    decodeBitMove din dout dα w = .query i x ↔
+      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) := by
+  refine ⟨fun h => ?_, fun h => h ▸ decodeBitMove_query din dout dα i x⟩
+  unfold decodeBitMove at h
+  split at h
+  · rename_i rest hw
+    split at h
+    · rename_i iw xw hr
+      split at h
+      · rename_i j hj
+        split at h
+        · rename_i x' hx
+          cases h
+          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr,
+            decodeIdx_eq_some_iff.1 hj, eq_ofFn_of_decodeFin hx]
+        · cases h
+      · cases h
+    · cases h
+  · split at h <;> cases h
+  · cases h
+
+/-- **The default:** a word that is neither a canonical query `⟨[false], ⟨1^i, x⟩⟩` nor a
+canonical output `⟨[true], a⟩` decodes to the output `zeroBits dα`. With `decodeBitMove_query`
+and `decodeBitMove_ret` this determines `decodeBitMove` on every word.
+
+**Proof sketch.** Follow `decodeBitMove`'s branches. Every branch but two returns `zeroBits dα`.
+In the query branch, the successful parses make `w` a canonical query word, as in
+`decodeBitMove_eq_query_iff`, against `hq`; in the output branch, they make `w` a canonical output
+word, against `hr`. -/
+theorem decodeBitMove_of_not_canonical {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
+    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
+      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
+    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
+    decodeBitMove din dout dα w = .ret (zeroBits dα) := by
+  unfold decodeBitMove
+  split
+  · rename_i rest hw
+    split
+    · rename_i iw xw hr'
+      split
+      · rename_i j hj
+        split
+        · rename_i x hx
+          refine absurd ?_ (hq j x)
+          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr',
+            decodeIdx_eq_some_iff.1 hj, eq_ofFn_of_decodeFin hx]
+        · rfl
+      · rfl
+    · rfl
+  · rename_i aw hw
+    split
+    · rename_i a ha
+      refine absurd ?_ (hr a)
+      rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_ofFn_of_decodeFin ha]
+    · rfl
+  · rfl
+
+/-- **Canonical words decode to their move:** `decodeBitMove (encodeBitMove m) = m`. -/
+theorem decodeBitMove_encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ)
+    (m : Move (bitSpec din dout) (Fin dα → Bool)) :
+    decodeBitMove din dout dα (encodeBitMove din dout dα m) = m := by
+  cases m with
+  | query i x => exact decodeBitMove_query din dout dα i x
+  | ret a => exact decodeBitMove_ret din dout dα a
+
+/-- Distinct moves have distinct canonical words. -/
+theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
+    Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
+  rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Bridges.lean b/TCSlib/Cryptography/Games/Bridges.lean
index b5a89e37..d16deb6f 100644
--- a/TCSlib/Cryptography/Games/Bridges.lean
+++ b/TCSlib/Cryptography/Games/Bridges.lean
@@ -25,7 +25,9 @@ model and to the ch. 2–4 layer.
 
 * `Games.Machines`: machines as oracle computations (`NUPPT.toComp`, `NUPPT.toCompOn`).
 * `Games.BitCodec`: bit-string oracles and their machine codec (`bitSpec`, `bitCodec`).
-* `Games.Efficiency`: polynomial-time handlers and the efficiency target T1 (the efficiency fill).
+* `Games.Efficiency`: polynomial-time handlers (adversary input, queries, finalization) and the
+  efficiency targets T1 and T2, with their companions (adversaries without input; T4, the bridge
+  to the ch. 2–4 next-query machines) (the efficiency fill).
 * `Games.Bridges.QueryTree`: the concrete layer's query trees, which *are* one-oracle computations
   (item F-1); their evaluation, simulation and query bounds are the framework's.
 * `Games.Bridges.Experiments`: the concrete layer's experiments (`invProb`, `predProb`,
diff --git a/TCSlib/Cryptography/Games/Bridges/Experiments.lean b/TCSlib/Cryptography/Games/Bridges/Experiments.lean
index 3b209800..5346a5a4 100644
--- a/TCSlib/Cryptography/Games/Bridges/Experiments.lean
+++ b/TCSlib/Cryptography/Games/Bridges/Experiments.lean
@@ -108,6 +108,13 @@ noncomputable def acceptGame [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty 
     (D : γ → ρ → Bool) : ProbComp Bool :=
   (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)
 
+/-- The acceptance game samples the seed `s`, then the coins `r`, and outputs `D (X s) r`:
+`acceptGame X D = (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)`. -/
+theorem acceptGame_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
+    (D : γ → ρ → Bool) :
+    acceptGame X D = (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r) :=
+  rfl
+
 /-- **Acceptance as a game:** `acceptProb X D` is the acceptance probability of `acceptGame X D`.
 [Gar26, Defs 3.2 and 3.4] -/
 theorem acceptProb_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
@@ -115,8 +122,8 @@ theorem acceptProb_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X :
   have h : acceptGame X D =
       (fun z : σ × ρ => D (X z.1) z.2) <$>
         ((sample σ).bind fun s => (sample ρ).bind fun r => .pure (s, r)) := by
-    simp only [acceptGame, OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
-  rw [acceptProb_def, accept, h, prob_eq_expect, expect_map, ← prob_eq_expect
+    simp only [acceptGame_eq, OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
+  rw [acceptProb_def, accept_eq, h, prob_eq_expect, expect_map, ← prob_eq_expect
     (p := fun z : σ × ρ => D (X z.1) z.2 = true), prob_sample_pair, prob_sample_eq_uprob]
 
 /-- **Distinguishing as a game:** `distAdv X Y D` is the advantage between the acceptance games
@@ -124,6 +131,6 @@ of `X` and of `Y`. [Gar26, Defs 3.2 and 3.4] -/
 theorem distAdv_eq [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ] [Fintype ρ] [Nonempty ρ]
     (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
     distAdv X Y D = advantage (acceptGame X D) (acceptGame Y D) := by
-  rw [distAdv_def, advantage, acceptProb_eq, acceptProb_eq]
+  rw [distAdv_def, advantage_eq, acceptProb_eq, acceptProb_eq]
 
 end TCSlib.Cryptography.Games.Bridge
diff --git a/TCSlib/Cryptography/Games/Bridges/Machines.lean b/TCSlib/Cryptography/Games/Bridges/Machines.lean
index 9030b32a..95aece6c 100644
--- a/TCSlib/Cryptography/Games/Bridges/Machines.lean
+++ b/TCSlib/Cryptography/Games/Bridges/Machines.lean
@@ -50,24 +50,70 @@ def singleCodec (ℓ₁ ℓ₂ : ℕ) :
   encodeEntry e := pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)
   timeout := false
 
+/-- The codec decodes a move with `decodeOracleMove`, the query `x` becoming a query to the sole
+oracle `()`: `(singleCodec ℓ₁ ℓ₂).decodeMove w` is `query () x` when `decodeOracleMove ℓ₁ w` is
+`query x`, and `ret b` when it is `ret b`. -/
+theorem singleCodec_decodeMove (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
+    (singleCodec ℓ₁ ℓ₂).decodeMove w = match decodeOracleMove ℓ₁ w with
+      | .query x => .query () x
+      | .ret b => .ret b :=
+  rfl
+
+/-- The codec encodes the log entry `(x, y)` as `⟨x, y⟩`, as `encodeHist` does. -/
+theorem singleCodec_encodeEntry (ℓ₁ ℓ₂ : ℕ)
+    (e : Σ u, (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).dom u ×
+      (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).rng u) :
+    (singleCodec ℓ₁ ℓ₂).encodeEntry e = pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2) :=
+  rfl
+
+/-- When the budget runs out, the codec's verdict is `false`. -/
+theorem singleCodec_timeout (ℓ₁ ℓ₂ : ℕ) : (singleCodec ℓ₁ ℓ₂).timeout = false :=
+  rfl
+
 /-- The ch. 2–4 history of a one-oracle log: the list of its (query, answer) pairs. -/
 def toHist {ℓ₁ ℓ₂ : ℕ} (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
     List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
   h.map fun e => (e.2.1, e.2.2)
 
+/-- The empty log has the empty history: `toHist [] = []`. -/
+theorem toHist_nil {ℓ₁ ℓ₂ : ℕ} :
+    toHist ([] : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) = [] :=
+  rfl
+
+/-- The history of `e :: h` starts with `e`'s (query, answer) pair:
+`toHist (e :: h) = (e.2.1, e.2.2) :: toHist h`. -/
+theorem toHist_cons {ℓ₁ ℓ₂ : ℕ}
+    (e : Σ u, (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).dom u ×
+      (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).rng u)
+    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
+    toHist (e :: h) = (e.2.1, e.2.2) :: toHist h :=
+  rfl
+
+/-- The history of `h ++ [e]` ends with `e`'s (query, answer) pair:
+`toHist (h ++ [e]) = toHist h ++ [(e.2.1, e.2.2)]`. -/
+theorem toHist_append_singleton {ℓ₁ ℓ₂ : ℕ}
+    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)))
+    (e : Σ u, (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).dom u ×
+      (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).rng u) :
+    toHist (h ++ [e]) = toHist h ++ [(e.2.1, e.2.2)] := by
+  rw [toHist, toHist, List.map_append, List.map_singleton]
+
 /-- The codec's log encoding is the ch. 2–4 history encoding. -/
 theorem encodeLog_singleCodec {ℓ₁ ℓ₂ : ℕ}
     (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
     (singleCodec ℓ₁ ℓ₂).encodeLog h = encodeHist (toHist h) := by
   induction h with
-  | nil => rfl
+  | nil => rw [MachineCodec.encodeLog_nil, toHist_nil, encodeHist_nil]
   | cons e h ih =>
-    simp only [MachineCodec.encodeLog, List.foldr_cons, toHist, List.map_cons, encodeHist] at ih ⊢
-    rw [ih]
-    rfl
+    rw [MachineCodec.encodeLog_cons, toHist_cons, encodeHist_cons, ih, singleCodec_encodeEntry]
 
 /-- One step of the correspondence: the framework's computation from a log is the ch. 2–4 tree
-from the corresponding history. -/
+from the corresponding history.
+
+**Proof sketch.** Induction on the budget. Both builders branch on the same move `next (toHist
+hist)`, by their case equations (`buildComp_zero_of_ret`, …, `buildTree_succ_of_query`): a verdict
+or a spent budget gives the same leaf, and a query gives a query node on both sides whose
+continuations agree by induction, since `toHist` of the extended log is the extended history. -/
 theorem buildComp_singleCodec {ℓ₁ ℓ₂ : ℕ}
     (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
     ∀ (q : ℕ) (hist : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))),
@@ -76,18 +122,20 @@ theorem buildComp_singleCodec {ℓ₁ ℓ₂ : ℕ}
           | .ret b => .ret b) false q hist =
         buildTree next q (toHist hist)
   | 0, hist => by
-    unfold buildComp buildTree
-    cases next (toHist hist) <;> rfl
+    cases hn : next (toHist hist) with
+    | ret b => rw [buildComp_zero_of_ret (a := b) (by simp only [hn]), buildTree_zero_of_ret hn]
+    | query x =>
+      rw [buildComp_zero_of_query (i := ()) (x := x) (by simp only [hn]),
+        buildTree_zero_of_query hn]
   | q + 1, hist => by
-    unfold buildComp buildTree
     cases hn : next (toHist hist) with
-    | ret b => rfl
+    | ret b => rw [buildComp_succ_of_ret (a := b) (by simp only [hn]), buildTree_succ_of_ret hn]
     | query x =>
-      dsimp only
-      congr 1
-      funext y
-      rw [buildComp_singleCodec next q]
-      simp [toHist]
+      rw [buildComp_succ_of_query (i := ()) (x := x) (by simp only [hn]),
+        buildTree_succ_of_query hn]
+      refine congrArg (OracleComp.query (spec := singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)) () x)
+        (funext fun y => ?_)
+      rw [buildComp_singleCodec next q, toHist_append_singleton]
 
 /-- **The ch. 2–4 decoder is an instance:** the oracle adversary `D.toOracleAdversary` of a
 next-query machine is its computation under `singleCodec`. So
@@ -103,10 +151,7 @@ theorem toComp_singleCodec (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) (r : D.Coins n)
         | .query x => Move.query () x
         | .ret b => Move.ret b) := by
     funext hist
-    rw [encodeLog_singleCodec]
-    rfl
-  simp only [NUPPT.toComp, NUPPT.toOracleAdversary]
-  rw [hnext]
-  exact h
+    rw [encodeLog_singleCodec, singleCodec_decodeMove]
+  rw [NUPPT.toComp_eq, NUPPT.toOracleAdversary_eq, hnext, singleCodec_timeout, h, toHist_nil]
 
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Bridges/QueryTree.lean b/TCSlib/Cryptography/Games/Bridges/QueryTree.lean
index be625b1e..420fe18e 100644
--- a/TCSlib/Cryptography/Games/Bridges/QueryTree.lean
+++ b/TCSlib/Cryptography/Games/Bridges/QueryTree.lean
@@ -66,6 +66,18 @@ def OracleComp.evalFn {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng
   | .pure a => a
   | .query i x k => evalFn f (k (f i x))
 
+/-- A return evaluates to its value: `(pure a).evalFn f = a`. -/
+theorem OracleComp.evalFn_pure {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i) (a : α) :
+    (OracleComp.pure a : OracleComp spec α).evalFn f = a :=
+  rfl
+
+/-- A query evaluates as its continuation on the answer `f i x`:
+`(query i x k).evalFn f = (k (f i x)).evalFn f`. -/
+theorem OracleComp.evalFn_query {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i)
+    (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) :
+    (OracleComp.query i x k).evalFn f = (k (f i x)).evalFn f :=
+  rfl
+
 /-- **Deterministic implementations evaluate:** simulating `c` with the stateless implementation
 that answers by the function `f` returns `c`'s output under `f` and leaves the state unchanged. -/
 theorem simulate_ofComp_pure {ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
@@ -73,8 +85,11 @@ theorem simulate_ofComp_pure {ι' : Type} {spec : OracleSpec ι} {spec' : Oracle
     simulate (QueryImpl.ofComp (σ := σ) (spec' := spec') fun i x => .pure (f i x)) c s =
       .pure (c.evalFn f, s) := by
   induction c with
-  | pure a => rfl
-  | query i x k ih => exact ih (f i x)
+  | pure a => rw [simulate_pure, OracleComp.evalFn_pure]
+  | query i x k ih =>
+    rw [simulate_query, QueryImpl.ofComp_apply, OracleComp.pure_bind, OracleComp.pure_bind,
+      OracleComp.evalFn_query]
+    exact ih (f i x)
 
 namespace Bridge
 
@@ -83,14 +98,24 @@ a one-oracle computation, with `f`. -/
 theorem eval_eq_evalFn (f : I → O) (t : TCSlib.Cryptography.QueryTree I O α) :
     t.eval f = OracleComp.evalFn (fun _ => f) t := by
   induction t using TCSlib.Cryptography.QueryTree.induct with
-  | ret a => rfl
-  | query x k ih => exact ih (f x)
+  | ret a => rw [TCSlib.Cryptography.QueryTree.eval_ret, OracleComp.evalFn_pure]
+  | query x k ih =>
+    rw [TCSlib.Cryptography.QueryTree.eval_query, OracleComp.evalFn_query]
+    exact ih (f x)
 
 /-- The implementation corresponding to `QueryTree.simulate π ans`: a query `x` is answered by
 asking `π x` of the new oracle and returning `ans x` of the answer; no state is used. -/
 def treeImpl (π : I → I') (ans : I → O' → O) : QueryImpl (singleSpec I O) σ (singleSpec I' O') :=
   QueryImpl.ofComp fun _ x => (OracleComp.call () (π x)).bind fun o' => .pure (ans x o')
 
+/-- The implementation answers the query `x` by asking `π x` and returning `ans x` of the answer,
+with the state `s` unchanged:
+`treeImpl π ans u x s = query () (π x) (fun o' => pure (ans x o', s))`. -/
+theorem treeImpl_apply (π : I → I') (ans : I → O' → O) (u : Unit) (x : I) (s : σ) :
+    treeImpl (σ := σ) π ans u x s = OracleComp.query () (π x) fun o' => .pure (ans x o', s) := by
+  rw [treeImpl, QueryImpl.ofComp_apply, OracleComp.bind_assoc, OracleComp.call_bind]
+  simp only [OracleComp.pure_bind]
+
 /-- **Garg's simulation is the framework's:** the tree `t.simulate π ans` is the framework's
 simulation of `t` by `treeImpl π ans`, with the (unchanged) state dropped.
 
@@ -100,12 +125,11 @@ theorem simulate_eq (π : I → I') (ans : I → O' → O) (t : TCSlib.Cryptogra
     (s : σ) :
     t.simulate π ans = (simulate (treeImpl π ans) t s).bind fun p => .pure p.1 := by
   induction t using TCSlib.Cryptography.QueryTree.induct with
-  | ret a => rfl
+  | ret a =>
+    rw [TCSlib.Cryptography.QueryTree.simulate_ret, simulate_pure, OracleComp.pure_bind]
   | query x k ih =>
-    show OracleComp.query () (π x) (fun o' => (k (ans x o')).simulate π ans) = _
-    simp only [simulate_query, treeImpl, QueryImpl.ofComp, ih, OracleComp.bind_assoc,
-      OracleComp.pure_bind]
-    rfl
+    rw [TCSlib.Cryptography.QueryTree.simulate_query, simulate_query, treeImpl_apply]
+    simp only [OracleComp.query_bind, OracleComp.pure_bind, ih]
 
 /-- **Query bounds are the framework's:** a tree makes at most `q` queries exactly when it is
 cost-bounded by `q` with every query costing one. -/
diff --git a/TCSlib/Cryptography/Games/Bridges/Strategies.lean b/TCSlib/Cryptography/Games/Bridges/Strategies.lean
index 08c76916..ef5461de 100644
--- a/TCSlib/Cryptography/Games/Bridges/Strategies.lean
+++ b/TCSlib/Cryptography/Games/Bridges/Strategies.lean
@@ -74,6 +74,12 @@ def turnParty (next : List Msg → Msg) : ℕ → List Msg → Party Msg Msg Msg
         | 0 => .pure (next M)
         | k' + 1 => turnParty next k' (M ++ [y])
 
+/-- With no moves left, the embedded party returns `next M`: `turnParty next 0 M = pure (next M)`.
+-/
+theorem turnParty_zero (next : List Msg → Msg) (M : List Msg) :
+    turnParty next 0 M = .pure (next M) :=
+  rfl
+
 /-- The embedded party **while waiting**, with `k` moves left (the other party's next one
 included) and received history `M`. On the other party's message `y` it takes its turn with
 `k − 1` moves left; on `none` (the other party has returned) it returns `next M`. -/
@@ -83,6 +89,22 @@ def waitParty (next : List Msg → Msg) (k : ℕ) (M : List Msg) : Option Msg 
     | 0 => .pure (next M)
     | k' + 1 => turnParty next k' (M ++ [y])
 
+/-- Waiting, on `none` (the other party has returned), the embedded party returns `next M`. -/
+theorem waitParty_none (next : List Msg → Msg) (k : ℕ) (M : List Msg) :
+    waitParty next k M none = .pure (next M) :=
+  rfl
+
+/-- Waiting with no moves left, a reply off schedule is ignored and the party returns `next M`. -/
+theorem waitParty_some_zero (next : List Msg → Msg) (M : List Msg) (y : Msg) :
+    waitParty next 0 M (some y) = .pure (next M) :=
+  rfl
+
+/-- Waiting with `k + 1` moves left, on the reply `y` the party appends it and takes its turn with
+`k` moves left: `waitParty next (k + 1) M (some y) = turnParty next k (M ++ [y])`. -/
+theorem waitParty_some_succ (next : List Msg → Msg) (k : ℕ) (M : List Msg) (y : Msg) :
+    waitParty next (k + 1) M (some y) = turnParty next k (M ++ [y]) :=
+  rfl
+
 /-- On its turn with `k + 1` moves left, the embedded party sends `next M` and then waits with
 `k` moves left. -/
 theorem turnParty_succ (next : List Msg → Msg) (k : ℕ) (M : List Msg) :
@@ -96,6 +118,16 @@ def alt (nF nG : List Msg → Msg) : ℕ → List Msg → List Msg → List Msg
   | 0, MF, MG => (MF, MG)
   | k + 1, MF, MG => (alt nG nF k (MG ++ [nF MF]) MF).swap
 
+/-- With no moves left, the histories are unchanged: `alt nF nG 0 MF MG = (MF, MG)`. -/
+theorem alt_zero (nF nG : List Msg → Msg) (MF MG : List Msg) : alt nF nG 0 MF MG = (MF, MG) :=
+  rfl
+
+/-- `alt`'s step at the front: `F` sends `nF MF` to `G`, then the roles are exchanged:
+`alt nF nG (k + 1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap`. -/
+theorem alt_succ (nF nG : List Msg → Msg) (k : ℕ) (MF MG : List Msg) :
+    alt nF nG (k + 1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap :=
+  rfl
+
 /-- `alt`'s step at the back: after `k + 1` moves, the last move is `F`'s when `k` is even (its
 message, computed on its history, is appended to `G`'s), and `G`'s when `k` is odd. This is D8's
 `exec_succ` shape.
@@ -135,14 +167,16 @@ theorem exec_turnParty : ∀ (k : ℕ) (nF nG : List Msg → Msg) (MF MG : List
       .pure (.done (nF (alt nF nG k MF MG).1) (nG (alt nF nG k MF MG).2)) := by
   intro k
   induction k with
-  | zero => intro nF nG MF MG; rfl
+  | zero =>
+    intro nF nG MF MG
+    simp only [turnParty_zero, Party.exec_zero, Party.step_pure, OracleComp.pure_bind,
+      Sum.elim_inl, Party.endWith_eq, waitParty_none, Party.close_pure, Option.elim_some,
+      alt_zero]
   | succ k ih =>
     intro nF nG MF MG
-    rw [turnParty_succ, Party.exec_succ]
-    show (Party.exec k (turnParty nG k (MG ++ [nF MF])) (waitParty nF k MF)).bind
-      (fun r => .pure r.swap) = _
-    rw [ih nG nF (MG ++ [nF MF]) MF]
-    rfl
+    simp only [turnParty_succ, Party.exec_succ, Party.step_send, OracleComp.pure_bind,
+      Sum.elim_inr, waitParty_some_succ, ih, ExecOutcome.swap_done, alt_succ, Prod.fst_swap,
+      Prod.snd_swap]
 
 /-- **D8's `exec` is `alt`:** after `k` moves from the empty histories, the messages received by
 `P` and by `V` are `alt`'s, with the first mover chosen by `vFirst`.
@@ -156,11 +190,13 @@ theorem exec_eq_alt (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
       if vFirst then (alt (V.next x zV rV) (P.next x zP rP) k [] []).swap
       else alt (P.next x zP rP) (V.next x zV rV) k [] [] := by
   induction k with
-  | zero => cases vFirst <;> rfl
+  | zero =>
+    cases vFirst <;>
+      simp only [exec_zero, alt_zero, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk]
   | succ k ih =>
     rw [exec_succ, ih]
     cases vFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [alt_succ_last] <;>
-      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [moverIsV, h]
+      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [moverIsV_true, moverIsV_false, h]
 
 /-- **A protocol's embedded execution returns D8's outputs:** for fixed tapes, running the first
 mover's embedding on its turn against the other's waiting embedding, with fuel the number of
@@ -180,12 +216,11 @@ theorem exec_strategies (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π
         else .done (π.outP x y z r) (π.outV π.P x y z r)) := by
   have hT := exec_eq_alt π.P π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
     (π.rounds.eval x.length)
-  simp only [Protocol.outP, Protocol.outV, Protocol.transcriptWith]
+  simp only [Protocol.outP_eq, Protocol.outV_eq, Protocol.transcriptWith_eq]
   cases hv : π.verifierFirst
   · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hT ⊢
     rw [exec_turnParty, hT]
   · simp only [hv, ↓reduceIte] at hT ⊢
-    rw [exec_turnParty, hT]
-    rfl
+    rw [exec_turnParty, hT, Prod.fst_swap, Prod.snd_swap]
 
 end TCSlib.Cryptography.Games.Bridge
diff --git a/TCSlib/Cryptography/Games/Efficiency.lean b/TCSlib/Cryptography/Games/Efficiency.lean
index 8c55fbbc..aeb8cff4 100644
--- a/TCSlib/Cryptography/Games/Efficiency.lean
+++ b/TCSlib/Cryptography/Games/Efficiency.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Games.BitCodec
 import TCSlib.Cryptography.Games.Probability
+import TCSlib.Cryptography.Games.Bridges.Machines
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -18,33 +19,76 @@ hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply t
 `briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`. The template is Frederick Dehmel's GGM
 reduction machine (`Asymptotic/GGMReduction*.lean`), whose loop `GGMRed.stateLoopFun` is reused.
 
-**Status: skeleton.** The definitions (T0) are final. The statements of T1 and T2 are frozen at the
-issue of the fill brief (`briefs/pass-shelat-ch5-8/fills/efficiency/`). Their proofs are the fill's.
+**Status: skeleton.** The definitions (T0) are final. The statements of T1, T2 and T4 and of the
+companion `exists_toCompOn_of_toComp` are frozen at the issue of the fill brief
+(`briefs/pass-shelat-ch5-8/fills/efficiency/`). Their proofs are the fill's.
+
+## The shape of a reduction
+
+A handler describes everything a reduction does around one run of the adversary. At parameter
+`n` the reduction has an input `z` and a seed `ω` (its own coins). Every function of the handler
+reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`):
+1. **the adversary's input** is a polynomial-time function of the context (`advIn`), for example
+   a public key built from `z` and `ω`; the adversary runs as `A.toCompOn` on it;
+2. **each query** of the adversary is answered from the handler's state, by the handler alone
+   (`PolyHandler`) or with queries to the reduction's own oracles (`InteractiveHandler`);
+3. **the reduction's output** is computed from the context, the final state and the adversary's
+   output: by a polynomial-time function (`PolyHandler.out`), or by a last phase that may itself
+   query the reduction's oracles, within its own budget (`InteractiveHandler.finish`).
 
 ## Fixed lengths
 
 Every length is an explicit polynomial in the parameter `n`: queries and answers (`din i`,
-`dout i`), the adversary's output (`dα`), and the handler's state and seed. This bounds every
-history, which the guarded state loop needs.
+`dout i`), the adversary's output (`dα`), the handler's state and seed, and, for an interactive
+handler, the reduction's output. This bounds every history, which the guarded state loop needs.
+
+## Scope
+
+* **Covered:** a reduction that runs one adversary once, on an input computed from its own,
+  answers the adversary's queries with or without its own oracles, and post-processes the final
+  state and the adversary's output (with further oracle queries if it is interactive). T1 makes
+  the machine's output exactly the finalized output; T2 makes the machine's computation exactly
+  the simulation followed by the finalization, with the budgets added.
+* **Adversaries without input** are adversaries with an input they ignore
+  (`exists_toCompOn_of_toComp`).
+* **Reductions to a pseudorandom function** reach `OracleEnsemble.Indist` through T4: an oracle
+  machine against one bit-string oracle with a one-bit output is, on evaluations, a next-query
+  machine of the ch. 2–4 layer (`NUPPT.toOracleAdversary`).
+* **Non-uniform handlers** (for example one that runs a non-uniform distinguisher) receive their
+  advice through the input `z`; it is hard-wired into the machine afterwards
+  (`NUPPT.exists_withAdvice`, with `NUPPT.exists_comp` to re-pair the input).
+* **Not covered:** reductions that rewind the adversary or run it more than once, and variable
+  lengths.
 
 ## Main definitions
 
+* `Games.seedIn n z ω`: the context `⟨1^n, ⟨z, ω⟩⟩`.
 * `Games.PolyHandler k din dout`: a polynomial-time handler for `k` bit-string oracles, with its
-  state and seed lengths and initial state.
+  state and seed lengths, initial state, adversary input and finalization.
 * `Games.PolyHandler.answer`, `Games.PolyHandler.impl`: its answers, and its semantics as a
-  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`.
+  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`;
+  `PolyHandler.advInput` and `PolyHandler.result`: the adversary's input and the reduction's
+  output.
 * `Games.InteractiveHandler`, `InteractiveHandler.call`, `InteractiveHandler.impl`: a
   polynomial-time handler that may itself query outer bit-string oracles, up to `perCall(n)`
-  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones.
+  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
+  `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
+  finalization, with up to `finCall(n)` outer queries.
 
 ## Main results
 
-* `Games.exists_handlerMachine` (T1, the fill's target): a machine adversary run against a
-  polynomial-time handler is a machine.
-* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a machine adversary run
-  against an interactive handler is an oracle machine against the outer oracles, with budget
-  `q(n) · perCall(n)`. The reductions that forward or answer queries with their own oracle need it
-  (the PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
+* `Games.exists_handlerMachine` (T1, the fill's target): a reduction with a polynomial-time
+  handler is a machine, whose output is exactly the finalized output of the simulation.
+* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a reduction with an
+  interactive handler is an oracle machine against the outer oracles, with budget
+  `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
+  finalization. The reductions that forward or answer queries with their own oracle need it (the
+  PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
+* `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
+  with an input that it ignores, with the same coins.
+* `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
+  against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
+  next-query machine of the ch. 2–4 layer.
 
 ## References
 
@@ -62,10 +106,32 @@ variable {k : ℕ}
 abbrev bitSpecAt (din dout : Fin k → PolyExpr) (n : ℕ) : OracleSpec (Fin k) :=
   bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)
 
+/-- The bit-string oracles at parameter `n` are `bitSpec` of the evaluated lengths:
+`bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)`. -/
+theorem bitSpecAt_eq (din dout : Fin k → PolyExpr) (n : ℕ) :
+    bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n) :=
+  rfl
+
+/-- The **context** of a reduction at parameter `n`, with the reduction's input `z` and its seed
+`ω`: the string `⟨1^n, ⟨z, ω⟩⟩`. Every function of a handler reads it. -/
+def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
+  pairEncode (List.replicate n true) (pairEncode z ω)
+
+/-- The context is `⟨1^n, ⟨z, ω⟩⟩`:
+`seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω)`. -/
+theorem seedIn_eq (n : ℕ) (z ω : List Bool) :
+    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) :=
+  rfl
+
 /-- A **polynomial-time handler** for `k` bit-string oracles with query lengths `din` and answer
-lengths `dout`. The function `run` is polynomial-time. On `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the
-parameter, the reduction's input `z`, its seed `ω`, the state `s`, and the query `x` to oracle
-`i`), it returns `⟨y, s'⟩`: the answer and the new state. -/
+lengths `dout`: a reduction that runs the adversary once and answers its queries by itself. Its
+three functions are polynomial-time, and each reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the
+parameter, the reduction's input `z` and its seed `ω`):
+- `advIn` maps the context to the adversary's input;
+- `run` answers one query: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the context, the state `s`, and
+  the query `x` to oracle `i`), it returns `⟨y, s'⟩`, the answer and the new state;
+- `out` maps `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the context, the final state and the adversary's output)
+  to the reduction's output. -/
 structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
   /-- The length of the state. -/
   stateLen : PolyExpr
@@ -77,6 +143,16 @@ structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
   run : List Bool → List Bool
   /-- It is polynomial-time computable. -/
   poly : PolyTimeComputable run
+  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩` (for example a public
+  key built from `z` and the seed). For an adversary without input it is ignored. -/
+  advIn : List Bool → List Bool
+  /-- The adversary's input is polynomial-time computable. -/
+  advIn_poly : PolyTimeComputable advIn
+  /-- The finalization: the reduction's output, as a function of `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the
+  context, the final state `s` and the adversary's output `a`). -/
+  out : List Bool → List Bool
+  /-- The finalization is polynomial-time computable. -/
+  out_poly : PolyTimeComputable out
 
 namespace PolyHandler
 
@@ -88,8 +164,48 @@ def input (n : ℕ) (z : List Bool) (ω : List Bool) (s : List Bool) (i : Fin k)
   pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
     (pairEncode s (pairEncode (List.replicate i true) x))
 
-/-- The handler's answer and new state, decoded with fixed lengths. A malformed output gives the
-all-`false` answer and state (a total default; well-behaved handlers never produce one). -/
+/-- The handler's input string is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩`. -/
+theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
+    input n z ω s i x =
+      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
+        (pairEncode s (pairEncode (List.replicate i true) x)) :=
+  rfl
+
+/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
+of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
+def advInput (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
+  H.advIn (seedIn n z (List.ofFn ω))
+
+/-- The adversary's input is `advIn` of the context:
+`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
+theorem advInput_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) :
+    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
+  rfl
+
+/-- The reduction's output at parameter `n`, for the reduction input `z` and the seed `ω`, when
+the final state is `s` and the adversary's output is `a`: `out` of
+`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`. -/
+def result (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
+    (a : Fin d → Bool) : List Bool :=
+  H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a)))
+
+/-- The reduction's output is `out` of the context, the final state and the adversary's output:
+`H.result n z ω s a = H.out (pairEncode (seedIn n z (List.ofFn ω))
+(pairEncode (List.ofFn s) (List.ofFn a)))`. -/
+theorem result_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
+    (a : Fin d → Bool) :
+    H.result n z ω s a =
+      H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a))) :=
+  rfl
+
+/-- The handler's answer and new state, decoded with fixed lengths. If `run`'s output is not a
+pair, both are all-`false`; otherwise each component of the wrong length is replaced by
+all-`false` independently (a total default; well-behaved handlers never produce one). An
+interactive handler defaults jointly instead (`InteractiveHandler`). -/
 def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
     (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
     (x : Fin ((din i).eval n) → Bool) :
@@ -99,6 +215,44 @@ def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
     ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
   | none => (zeroBits _, zeroBits _)
 
+section Answer
+
+variable (H : PolyHandler k din dout) {n : ℕ} {z : List Bool} {ω : Fin (H.seedLen.eval n) → Bool}
+  {s : Fin (H.stateLen.eval n) → Bool} {i : Fin k} {x : Fin ((din i).eval n) → Bool}
+
+/-- If `run`'s output is not a pair, the answer and the new state are all-`false`. -/
+theorem answer_of_pairDecode_eq_none
+    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) = none) :
+    H.answer n z ω s i x = (zeroBits _, zeroBits _) := by
+  unfold answer
+  rw [h]
+
+/-- If `run`'s output is the pair `⟨yw, sw⟩`, the answer is `yw` and the new state `sw`, each
+decoded with its fixed length and all-`false` if that length is wrong:
+`H.answer n z ω s i x = ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`.
+-/
+theorem answer_of_pairDecode_eq_some {yw sw : List Bool}
+    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
+      some (yw, sw)) :
+    H.answer n z ω s i x =
+      ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _)) := by
+  unfold answer
+  rw [h]
+
+/-- **A well-formed output:** if `run` returns `⟨y, s'⟩` with `y` and `s'` of the fixed lengths,
+the answer is `y` and the new state `s'`. -/
+theorem answer_of_run_eq {y : Fin ((dout i).eval n) → Bool} {s' : Fin (H.stateLen.eval n) → Bool}
+    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)) =
+      pairEncode (List.ofFn y) (List.ofFn s')) :
+    H.answer n z ω s i x = (y, s') := by
+  have h' : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
+      some (List.ofFn y, List.ofFn s') := by
+    rw [h, pairDecode_pairEncode]
+  rw [answer_of_pairDecode_eq_some H h', decodeFin_ofFn, decodeFin_ofFn, Option.getD_some,
+    Option.getD_some]
+
+end Answer
+
 /-- The handler as an implementation of the bit-string oracles at parameter `n`, for the
 reduction input `z` and seed `ω`: it keeps its state and asks no oracle (the non-interactive
 case). -/
@@ -107,35 +261,52 @@ def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
     QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
   fun i x s => .pure (H.answer n z ω s i x)
 
+/-- The handler answers the query `x` to oracle `i` in state `s` with no coins and no queries:
+`H.impl n z ω i x s = pure (H.answer n z ω s i x)`. -/
+theorem impl_apply (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
+    (s : Fin (H.stateLen.eval n) → Bool) :
+    H.impl n z ω i x s = .pure (H.answer n z ω s i x) :=
+  rfl
+
 end PolyHandler
 
 /-- **T1 (the efficiency fill's target; non-interactive handlers).** For a machine adversary `A`
 with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and a polynomial-time
 handler `H`, there is a machine `B` and, at every parameter, a bijection `φ` from (the handler's
-seed, `A`'s coins) to `B`'s coins, such that `B`'s output on input `z` and coins `φ (ω, r)` is
-`A`'s output when `A`'s queries are answered by `H` (input `z`, seed `ω`), from `H`'s initial
-state.
+seed, `A`'s coins) to `B`'s coins, with the following property. Run `A` on the input
+`H.advInput n z ω`, answer its queries by `H` (input `z`, seed `ω`) from `H`'s initial state, and
+let `a` be `A`'s output and `s` the final state. Then `B`'s output on input `z` with coins
+`φ (ω, r)` is exactly the reduction's output `H.result n z ω s a`.
 
 **Proof sketch** (the fill's; route note §"The route", steps 1–4 without the log replay):
-1. `B`'s round function, on `⟨1^n, z, ω, r, history, state⟩`, runs `A`'s next-move function on
-   the encoded history (`NUPPT.polyTimeComputable_output`), decodes the move (`decodeBitMove`), and
-   either feeds the query to `H.run` (polynomial-time by `H.poly`), appending the answer and the new
-   state, or stops with `A`'s output.
-2. `GGMRed.stateLoopFun` runs at most `q(n) + 1` rounds; `stateLoopFun_poly` makes it
+1. `B`'s first step computes `A`'s input `H.advIn (seedIn n z ω)` (polynomial-time by
+   `H.advIn_poly`; so its length is polynomial in `n + |z|`), and keeps it in the loop state.
+2. `B`'s round function, on `⟨1^n, z, ω, r, A's input, history, state⟩`, runs `A`'s next-move
+   function on `⟨A's input, encoded history⟩` (`NUPPT.polyTimeComputable_output`), decodes the
+   move (`decodeBitMove`, read through `decodeBitMove_eq_query_iff` and
+   `decodeBitMove_of_not_canonical`), and either feeds the query to `H.run` (polynomial-time by
+   `H.poly`), appending the answer and the new state, or stops with `A`'s output and the state.
+3. `GGMRed.stateLoopFun` runs at most `q(n) + 1` rounds; `stateLoopFun_poly` makes it
    polynomial-time, given that the histories stay below a polynomial (all lengths are fixed).
-3. `B := NUPPT.ofPolyTime` of the loop, with the coins split as `(ω, r)` by `exists_split`
+   The loop's result `(a, s)` is finalized by `H.out` on `⟨seedIn n z ω, ⟨s, a⟩⟩`
+   (polynomial-time by `H.out_poly`).
+4. `B := NUPPT.ofPolyTime` of the composite, with the coins split as `(ω, r)` by `exists_split`
    (`Complexity/Randomized/Closure.lean`).
-4. The functional equation: by induction on the remaining budget, the loop's state after `t`
-   rounds is the simulation's state after `t` queries (`buildComp`'s unfolding against
-   `simulate_query`); `stateLoopFun_eval` reads off the output. -/
+5. The functional equation: by induction on the remaining budget, the loop's state after `t`
+   rounds is the simulation's state after `t` queries (`toCompOn_eq` and `buildComp`'s case
+   lemmas against `simulate_query`, `PolyHandler.impl_apply` and the `answer` lemmas);
+   `stateLoopFun_eval` reads off `(a, s)`, and `result_eq` the output. -/
 theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
     (dα : PolyExpr) (H : PolyHandler k din dout) :
     ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
       ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
-        ∃ s, simulate (H.impl n z ω)
-            (A.toComp (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
-              n (q.eval n) r) (H.init n) =
-          .pure (padFin (dα.eval n) (B.runAt n z (φ (ω, r))), s) := by
+        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
+          simulate (H.impl n z ω)
+              (A.toCompOn
+                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
+                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
+            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
   sorry
 
 /-! ### Interactive handlers (T2) -/
@@ -143,11 +314,23 @@ theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → P
 variable {k' : ℕ}
 
 /-- A **polynomial-time interactive handler** for `k` inner bit-string oracles that may itself
-query `k'` outer bit-string oracles. One inner query `x` to oracle `i` is answered in up to
-`perCall(n)` rounds of `run`. In each round, `run` sees
-`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is the outer log of the call so far (encoded as
-`bitCodec` encodes logs), and returns a move in `bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩`
-to outer oracle `j`, or the answer `⟨[true], y ‖ s'⟩` (the inner answer, then the new state). -/
+query `k'` outer bit-string oracles. Like `PolyHandler`, it computes the adversary's input from
+the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queries (`run`), and computes the
+reduction's output in a last phase (`finRun`), both with outer queries.
+
+One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
+`perCall(n) + 1` rounds of `run` (the last returns the answer or, with the budget spent, is cut off
+with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
+the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
+`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
+`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
+payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
+joint default, unlike `PolyHandler.answer`, which defaults each component separately).
+
+The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
+adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
+queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
+output on a malformed round output or a spent budget. -/
 structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
     (din' dout' : Fin k' → PolyExpr) where
   /-- The length of the state. -/
@@ -162,6 +345,20 @@ structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ
   run : List Bool → List Bool
   /-- It is polynomial-time computable. -/
   poly : PolyTimeComputable run
+  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩`. For an adversary
+  without input it is ignored. -/
+  advIn : List Bool → List Bool
+  /-- The adversary's input is polynomial-time computable. -/
+  advIn_poly : PolyTimeComputable advIn
+  /-- The length of the reduction's output. -/
+  outLen : PolyExpr
+  /-- The bound on the outer queries of the finalization. -/
+  finCall : PolyExpr
+  /-- One round of the finalization, as a string function: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` it
+  returns an outer query `⟨[false], ⟨1^j, x'⟩⟩` or the reduction's output `⟨[true], b⟩`. -/
+  finRun : List Bool → List Bool
+  /-- The finalization's round is polynomial-time computable. -/
+  finRun_poly : PolyTimeComputable finRun
 
 namespace InteractiveHandler
 
@@ -172,9 +369,29 @@ def input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) : List Bo
   pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
     (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L))
 
-/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: up to
-`perCall(n)` rounds against the outer oracles. A malformed round output is the all-`false`
-answer and state (`decodeBitMove`'s default), and so is an exhausted budget. -/
+/-- The handler's input string for one round is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
+theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
+    input n z ω s i x L =
+      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
+        (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
+  rfl
+
+/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
+of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
+def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
+  H.advIn (seedIn n z (List.ofFn ω))
+
+/-- The adversary's input is `advIn` of the context:
+`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
+theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) :
+    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
+  rfl
+
+/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
+`perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
+is the all-`false` answer and state (`decodeBitMove`'s default), and so is an exhausted budget. -/
 def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
     (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
     (x : Fin ((din i).eval n) → Bool) :
@@ -184,6 +401,21 @@ def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List B
         ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
     (zeroBits _) (H.perCall.eval n) []
 
+/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
+`perCall(n)` and the all-`false` result when it runs out: `H.call n z ω s i x =
+buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
+-/
+theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
+    (x : Fin ((din i).eval n) → Bool) :
+    H.call n z ω s i x =
+      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
+          ((dout i).eval n + H.stateLen.eval n)
+          (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
+            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
+        (zeroBits _) (H.perCall.eval n) [] :=
+  rfl
+
 /-- The interactive handler as an implementation of the inner oracles by the outer ones, at
 parameter `n`, reduction input `z` and seed `ω`: one `call` per inner query, its result split
 into the answer and the new state. -/
@@ -193,38 +425,150 @@ def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List B
   fun i x s => (H.call n z ω s i x).bind fun w =>
     .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))
 
+/-- The inner query `x` to oracle `i` in state `s` is answered by one `call`, whose result is
+split into the answer (its first `dout i` bits) and the new state (the rest):
+`H.impl n z ω i x s = (H.call n z ω s i x).bind fun w =>
+pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))`. -/
+theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
+    (s : Fin (H.stateLen.eval n) → Bool) :
+    H.impl n z ω i x s =
+      (H.call n z ω s i x).bind fun w =>
+        .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
+  rfl
+
+/-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
+final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
+def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
+  pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))
+
+/-- The input string of one round of the finalization is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
+`finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))`. -/
+theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
+    finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
+  rfl
+
+/-- **The finalization** in the final state `s`, after the adversary's output `a`: the
+reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
+`finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
+(`decodeBitMove`'s default), and so is an exhausted budget. -/
+def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
+    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
+  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
+      (H.outLen.eval n)
+      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
+    (zeroBits _) (H.finCall.eval n) []
+
+/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
+`finCall(n)` and the all-`false` output when it runs out: `H.finish n z ω s a =
+buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
+(H.finCall.eval n) []`. -/
+theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
+    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
+    (a : Fin d → Bool) :
+    H.finish n z ω s a =
+      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
+          (H.outLen.eval n)
+          (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
+        (zeroBits _) (H.finCall.eval n) [] :=
+  rfl
+
 end InteractiveHandler
 
 /-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
 with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and an interactive
 handler `H` answering them through `k'` outer oracles, there is an oracle machine `B` against the
-outer oracles, with budget `q(n) · perCall(n)`, and at every parameter a bijection `φ` from
-(`H`'s seed, `A`'s coins) to `B`'s coins, such that `B` on input `z` with coins `φ (ω, r)` is, as
-an oracle computation, `A`'s computation simulated by `H` (input `z`, seed `ω`) from `H`'s initial
-state, outputs only.
+outer oracles, with budget `q(n) · perCall(n) + finCall(n)`, and at every parameter a bijection
+`φ` from (`H`'s seed, `A`'s coins) to `B`'s coins, with the following property. `B` on input `z`
+with coins `φ (ω, r)` is, as an oracle computation, exactly the reduction: `A` run on the input
+`H.advInput n z ω`, its queries answered by `H` (input `z`, seed `ω`) from `H`'s initial state,
+followed by `H`'s finalization on the final state and `A`'s output.
 
 **Proof sketch** (the fill's; route note §"The route", with the log replay).
-1. `B`'s next-move function, on `⟨z, outer log⟩`, replays: it splits the outer log into the
-   calls of `H`. Within each call, it reruns `H.run` round by round, and between calls it reruns
-   `A`'s next-move function on the inner log rebuilt from the calls' answers. It stops at the first
-   pending outer query (and asks it) or at `A`'s output (and returns it). Every length is fixed,
-   so each replay is polynomial (`stateLoopFun_poly`, as in T1).
+1. `B`'s next-move function, on `⟨z, outer log⟩` with coins `(ω, r)`, first computes `A`'s input
+   `H.advIn (seedIn n z ω)` (`H.advIn_poly`). It then replays: it splits the outer log into the
+   calls of `H` and the finalization. Within each call it reruns `H.run` round by round, and
+   between calls it reruns `A`'s next-move function on `⟨A's input, inner log⟩`, the inner log
+   rebuilt from the calls' answers. Once `A` returns `a` (or meets its own budget), it reruns
+   `H.finRun` on `⟨seedIn n z ω, ⟨s, ⟨a, L⟩⟩⟩` with the rest `L` of the log. It stops at the first
+   pending outer query (and asks it) or at the finalization's output (and returns its canonical
+   word, `encodeBitMove`). Every length is fixed, so each replay is polynomial
+   (`stateLoopFun_poly`, as in T1).
 2. `B`'s budget suffices: each of `A`'s at most `q(n)` queries costs at most `perCall(n)` outer
-   queries (`buildComp_costBoundedBy`), so `B` never meets its own timeout before `A` or a call
-   does, and it mirrors both defaults.
+   queries and the finalization at most `finCall(n)` (`buildComp_costBoundedBy`,
+   `simulate_costBoundedBy`, `CostBoundedBy.bind`), so `B` never meets its own timeout before
+   the reduction ends, and it mirrors every default of `A`, of a call and of the finalization.
 3. The functional equation: by induction on the outer log, the two computation trees agree node
-   by node (`simulate_query`, `buildComp`'s unfolding). Coins split as `(ω, r)` by
-   `exists_split`. -/
+   by node (`simulate_query`, `impl_apply`, `call_eq`, `finish_eq`, `toCompOn_eq`, `buildComp`'s
+   case lemmas, `decodeBitMove_encodeBitMove`). Coins split as `(ω, r)` by `exists_split`. -/
 theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
     (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
     (H : InteractiveHandler k din dout k' din' dout') :
     ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
       ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
         (simulate (H.impl n z ω)
-            (A.toComp (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
-              n (q.eval n) r) (H.init n)).bind (fun res => .pure res.1) =
-          B.toCompOn (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (dα.eval n))
-            n (q.eval n * H.perCall.eval n) z (φ (ω, r)) := by
+            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
+              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
+            (fun res => H.finish n z ω res.2 res.1) =
+          B.toCompOn
+            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
+            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
+  sorry
+
+/-! ### Companions: adversaries without input, and the bridge to pseudorandom functions (T4) -/
+
+/-- **A machine without input is a machine with an input that it ignores.** For every machine
+`A` there is a machine `A'` with the same coins whose computation on any input `x` is `A`'s
+computation, for every codec and budget, the coins related by a bijection `φ`. So T1 and T2,
+stated for adversaries with input, cover adversaries without one.
+
+**Proof sketch.** `A'` is `NUPPT.exists_comp` of `A` with `pre = pairSndD` and `post = id`, so
+`A'.coins = A.coins` and `A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). The
+bijection `φ` transports the coins along `A.coinLen n = A'.coinLen n` (`finCongr`), so
+`List.ofFn (φ r) = List.ofFn r` (`List.ofFn_congr`); with `runAt_eq` the next-move functions of
+`A'.toCompOn codec n q x (φ r)` and `A.toComp codec n q r` agree on every log, and
+`toCompOn_eq`, `toComp_eq` conclude. The length equation needs an equation of `NUPPT.coinLen`,
+published beside its definition. -/
+theorem exists_toCompOn_of_toComp (A : NUPPT) :
+    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
+      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
+        (x : List Bool) (r : A.Coins n),
+        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
+  sorry
+
+/-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
+machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
+one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
+machine `B'` with the same coins whose oracle adversary `B'.toOracleAdversary`, run against any
+`f`, returns the bit of `B`'s computation evaluated with `f`, the coins related by a bijection
+`φ`. So `OracleEnsemble.Indist`, and with it `PRF`, applies to the machines of T2 with one outer
+oracle and a one-bit output (through `oracleDist_apply` and `Bridge.eval_eq_evalFn`).
+
+**Proof sketch.**
+1. `B'` translates between the two formats around `B` (`NUPPT.exists_comp` with polynomial-time
+   pre- and post-processing, or `NUPPT.ofPolyTime` of the composite to read `1^{ℓ₁(n)}`):
+   - its input, the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`), becomes `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩,
+     ⟨…, []⟩⟩⟩`, `B`'s empty input and its log (`encodeHist_cons`, `encodeLog_cons`,
+     `bitCodec_encodeEntry` with `1^0 = []`), polynomial-time by iterating over the pairs;
+   - `B`'s output, a move decoded by `decodeBitMove` (`decodeBitMove_eq_query_iff`,
+     `decodeBitMove_of_not_canonical`, `decodeIdx_eq_some_iff` at `k = 1`), becomes the query
+     `⟨[false], x⟩` for a query `x`, and the verdict `[true, b]` for an output `[b]` and for the
+     default.
+2. Both trees branch on corresponding moves, so by induction on the budget
+   (`toOracleAdversary_eq` and `buildTree`'s case lemmas against `toCompOn_eq` and `buildComp`'s)
+   their evaluations against `f` and `fun _ => f` agree (`QueryTree.eval_query`,
+   `OracleComp.evalFn_query`); at the timeout the verdict `false` is bit `0` of `zeroBits 1`
+   (`zeroBits_apply`).
+3. `φ` transports the coins along `B.coins = B'.coins`, as in `exists_toCompOn_of_toComp`. -/
+theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
+    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
+      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
+        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
+          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
+              r).evalFn (fun _ => f) 0 := by
   sorry
 
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Hopping.lean b/TCSlib/Cryptography/Games/Hopping.lean
index 4159d1c8..3a6a3130 100644
--- a/TCSlib/Cryptography/Games/Hopping.lean
+++ b/TCSlib/Cryptography/Games/Hopping.lean
@@ -82,10 +82,13 @@ then the expectation of `f` over `c` is at most that of `g`. -/
 theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
     {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
   induction c with
-  | pure a => exact h a hc
+  | pure a =>
+    rw [expect_pure, expect_pure]
+    exact h a (OracleComp.allOutputs_pure.1 hc)
   | query m x k ih =>
     simp only [expect_query]
-    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j (hc j)) (by positivity)
+    exact mul_le_mul_of_nonneg_left
+      (sum_le_sum fun j _ => ih j (OracleComp.allOutputs_query.1 hc j)) (by positivity)
 
 /-- An event holding at every possible output has probability one. -/
 theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
@@ -165,7 +168,9 @@ theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ
     (c : OracleComp spec α) {s : σ} (hs : bad s) :
     (simulate impl c s).AllOutputs fun r => bad r.2 := by
   induction c generalizing s with
-  | pure a => exact hs
+  | pure a =>
+    rw [simulate_pure, OracleComp.allOutputs_pure]
+    exact hs
   | query i x k ih =>
     rw [simulate_query]
     exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys
@@ -210,7 +215,7 @@ theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl sp
       ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
         ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
   induction c generalizing s with
-  | pure a => exact ⟨rfl, rfl⟩
+  | pure a => simp only [simulate_pure, and_self]
   | query i x k ih =>
     simp only [simulate_query, ProbComp.prob_bind]
     constructor
diff --git a/TCSlib/Cryptography/Games/Machines.lean b/TCSlib/Cryptography/Games/Machines.lean
index a1663582..3bc7de06 100644
--- a/TCSlib/Cryptography/Games/Machines.lean
+++ b/TCSlib/Cryptography/Games/Machines.lean
@@ -89,6 +89,17 @@ variable {spec : OracleSpec ι}
 def encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) : List Bool :=
   h.foldr (fun e acc => pairEncode (codec.encodeEntry e) acc) []
 
+/-- The empty log is encoded as the empty string: `codec.encodeLog [] = []`. -/
+theorem encodeLog_nil (codec : MachineCodec spec α) : codec.encodeLog [] = [] :=
+  rfl
+
+/-- A log is encoded entry by entry:
+`codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h)`. -/
+theorem encodeLog_cons (codec : MachineCodec spec α) (e : Σ i, spec.dom i × spec.rng i)
+    (h : QueryLog spec) :
+    codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h) :=
+  rfl
+
 end MachineCodec
 
 /-- The computation of a next-move function `next` with query budget `q`, started from the log
@@ -103,18 +114,55 @@ def buildComp {spec : OracleSpec ι} (next : QueryLog spec → Move spec α) (ti
     | .ret a => .pure a
     | .query i x => .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))
 
+section BuildComp
+
+variable {spec : OracleSpec ι} {next : QueryLog spec → Move spec α} {timeout : α}
+  {hist : QueryLog spec}
+
+/-- With the budget spent, a final output stops the computation:
+`buildComp next timeout 0 hist = pure a` when `next hist = ret a`. -/
+theorem buildComp_zero_of_ret {a : α} (h : next hist = .ret a) :
+    buildComp next timeout 0 hist = .pure a := by
+  rw [buildComp, h]
+
+/-- With the budget spent, a query gives the output `timeout` and asks nothing:
+`buildComp next timeout 0 hist = pure timeout` when `next hist = query i x`. -/
+theorem buildComp_zero_of_query {i : ι} {x : spec.dom i} (h : next hist = .query i x) :
+    buildComp next timeout 0 hist = .pure timeout := by
+  rw [buildComp, h]
+
+/-- Within budget, a final output stops the computation:
+`buildComp next timeout (q + 1) hist = pure a` when `next hist = ret a`. -/
+theorem buildComp_succ_of_ret {q : ℕ} {a : α} (h : next hist = .ret a) :
+    buildComp next timeout (q + 1) hist = .pure a := by
+  rw [buildComp, h]
+
+/-- Within budget, a query asks the oracle and continues with the entry appended to the log:
+`buildComp next timeout (q + 1) hist =
+query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))` when `next hist = query i x`.
+-/
+theorem buildComp_succ_of_query {q : ℕ} {i : ι} {x : spec.dom i} (h : next hist = .query i x) :
+    buildComp next timeout (q + 1) hist =
+      .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩])) := by
+  rw [buildComp, h]
+
+end BuildComp
+
 /-- The computation built with budget `q` makes at most `q` queries, from every log. -/
 theorem buildComp_costBoundedBy {spec : OracleSpec ι} (next : QueryLog spec → Move spec α)
     (timeout : α) : ∀ (q : ℕ) (hist : QueryLog spec),
       (buildComp next timeout q hist).CostBoundedBy (fun _ => 1) q
   | 0, hist => by
-    unfold buildComp
-    cases next hist <;> exact trivial
+    cases h : next hist with
+    | ret a => rw [buildComp_zero_of_ret h]; exact OracleComp.costBoundedBy_pure _ _ _
+    | query i x => rw [buildComp_zero_of_query h]; exact OracleComp.costBoundedBy_pure _ _ _
   | q + 1, hist => by
-    unfold buildComp
-    cases next hist with
-    | ret a => exact trivial
-    | query i x => exact ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩
+    cases h : next hist with
+    | ret a => rw [buildComp_succ_of_ret h]; exact OracleComp.costBoundedBy_pure _ _ _
+    | query i x =>
+      rw [buildComp_succ_of_query h]
+      exact (OracleComp.costBoundedBy_query _ _ _ _ _).2
+        ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩
 
 /-- The oracle computation of the machine `D` at parameter `n`, with coins `r` and query budget
 `q`: the machine's next-move function is one activation of `D` on the encoded log.
@@ -123,6 +171,17 @@ def _root_.Complexity.NUPPT.toComp {spec : OracleSpec ι} (D : NUPPT) (codec : M
     (n q : ℕ) (r : D.Coins n) : OracleComp spec α :=
   buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []
 
+/-- The computation of `D` is built from the empty log, the next move being `D`'s output on the
+encoded log, decoded: `D.toComp codec n q r =
+buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []`.
+-/
+theorem _root_.Complexity.NUPPT.toComp_eq {spec : OracleSpec ι} (D : NUPPT)
+    (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
+    D.toComp codec n q r =
+      buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout
+        q [] :=
+  rfl
+
 /-- A machine's computation makes at most `q` queries. -/
 theorem _root_.Complexity.NUPPT.toComp_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
     (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
@@ -137,6 +196,17 @@ def _root_.Complexity.NUPPT.toCompOn {spec : OracleSpec ι} (D : NUPPT)
   buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
     codec.timeout q []
 
+/-- The computation of `D` on the input `x` is built from the empty log, the next move being
+`D`'s output on `⟨x, encoded log⟩`, decoded: `D.toCompOn codec n q x r =
+buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
+codec.timeout q []`. -/
+theorem _root_.Complexity.NUPPT.toCompOn_eq {spec : OracleSpec ι} (D : NUPPT)
+    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) :
+    D.toCompOn codec n q x r =
+      buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
+        codec.timeout q [] :=
+  rfl
+
 /-- A machine's computation on an input makes at most `q` queries. -/
 theorem _root_.Complexity.NUPPT.toCompOn_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
     (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) :
diff --git a/TCSlib/Cryptography/Games/OracleComp.lean b/TCSlib/Cryptography/Games/OracleComp.lean
index 24cbd565..2b8c0460 100644
--- a/TCSlib/Cryptography/Games/OracleComp.lean
+++ b/TCSlib/Cryptography/Games/OracleComp.lean
@@ -154,6 +154,12 @@ end OracleComp
 layer's query trees are the computations over it (`TCSlib.Cryptography.QueryTree`). -/
 abbrev singleSpec (I O : Type) : OracleSpec Unit := ⟨fun _ => I, fun _ => O⟩
 
+/-- The single oracle of `singleSpec I O` takes queries in `I`. -/
+theorem singleSpec_dom (I O : Type) (u : Unit) : (singleSpec I O).dom u = I := rfl
+
+/-- The single oracle of `singleSpec I O` answers in `O`. -/
+theorem singleSpec_rng (I O : Type) (u : Unit) : (singleSpec I O).rng u = O := rfl
+
 /-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
 oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
 def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
@@ -269,6 +275,18 @@ def AllOutputs {spec : OracleSpec ι} (P : α → Prop) : OracleComp spec α →
   | .pure a => P a
   | .query _ _ k => ∀ y, AllOutputs P (k y)
 
+/-- The only possible output of a return is its value: `(pure a).AllOutputs P ↔ P a`. -/
+theorem allOutputs_pure {spec : OracleSpec ι} {P : α → Prop} {a : α} :
+    (OracleComp.pure (spec := spec) a).AllOutputs P ↔ P a :=
+  Iff.rfl
+
+/-- The possible outputs of a query are those of its continuations, whatever the answer:
+`(query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P`. -/
+theorem allOutputs_query {spec : OracleSpec ι} {P : α → Prop} {i : ι} {x : spec.dom i}
+    {k : spec.rng i → OracleComp spec α} :
+    (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P :=
+  Iff.rfl
+
 /-- Every computation satisfies the trivial predicate at every possible output. -/
 theorem allOutputs_true {spec : OracleSpec ι} (c : OracleComp spec α) :
     c.AllOutputs fun _ => True := by
diff --git a/TCSlib/Cryptography/Games/Protocols.lean b/TCSlib/Cryptography/Games/Protocols.lean
index 1b84c70b..3e6d9334 100644
--- a/TCSlib/Cryptography/Games/Protocols.lean
+++ b/TCSlib/Cryptography/Games/Protocols.lean
@@ -103,6 +103,21 @@ def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
   | .outOfFuel => .outOfFuel
   | .sentAfterEnd => .sentAfterEnd
 
+/-- Exchanging the roles exchanges the outputs: `(done a b).swap = done b a`. -/
+theorem ExecOutcome.swap_done {α β : Type} (a : α) (b : β) :
+    (ExecOutcome.done a b).swap = .done b a :=
+  rfl
+
+/-- A spent budget stays a spent budget: `outOfFuel.swap = outOfFuel`. -/
+theorem ExecOutcome.swap_outOfFuel {α β : Type} :
+    (ExecOutcome.outOfFuel : ExecOutcome α β).swap = .outOfFuel :=
+  rfl
+
+/-- A send after the end stays one: `sentAfterEnd.swap = sentAfterEnd`. -/
+theorem ExecOutcome.swap_sentAfterEnd {α β : Type} :
+    (ExecOutcome.sentAfterEnd : ExecOutcome α β).swap = .sentAfterEnd :=
+  rfl
+
 namespace Party
 
 variable {Out In α β : Type}
@@ -114,6 +129,24 @@ def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out
   | .query (.inl ()) m k => .pure (.inr (m, k))
   | .query (.inr j) x k => .query j x (fun y => step (k y))
 
+/-- A returned party is done: `step (pure a) = pure (inl a)`. -/
+theorem step_pure (a : α) : step (OracleComp.pure a : Party Out In α) = .pure (.inl a) :=
+  rfl
+
+/-- A party sending `m` stops there, with `m` and its continuation on the reply:
+`step (query (inl ()) m k) = pure (inr (m, k))`. -/
+theorem step_send (m : Out) (k : Option In → Party Out In α) :
+    step (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inl ()) m k) =
+      .pure (.inr (m, k)) :=
+  rfl
+
+/-- A coin draw of a party is passed through:
+`step (query (inr j) x k) = query j x (fun y => step (k y))`. -/
+theorem step_coin (j : ℕ) (x : Unit) (k : Fin (j + 1) → Party Out In α) :
+    step (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inr j) x k) =
+      .query j x (fun y => step (k y)) :=
+  rfl
+
 /-- **Close** a party whose counterpart has returned (its pending send already answered `none`):
 it may still draw coins, and returns `some` of its output, or `none` if it sends a message. -/
 def close : Party Out In α → ProbComp (Option α)
@@ -121,12 +154,37 @@ def close : Party Out In α → ProbComp (Option α)
   | .query (.inl ()) _ _ => .pure none
   | .query (.inr j) x k => .query j x (fun y => close (k y))
 
+/-- Closing a returned party gives its output: `close (pure a) = pure (some a)`. -/
+theorem close_pure (a : α) : close (OracleComp.pure a : Party Out In α) = .pure (some a) :=
+  rfl
+
+/-- Closing a party that sends gives `none`: `close (query (inl ()) m k) = pure none`. -/
+theorem close_send (m : Out) (k : Option In → Party Out In α) :
+    close (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inl ()) m k) =
+      .pure none :=
+  rfl
+
+/-- Closing passes a coin draw through:
+`close (query (inr j) x k) = query j x (fun y => close (k y))`. -/
+theorem close_coin (j : ℕ) (x : Unit) (k : Fin (j + 1) → Party Out In α) :
+    close (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inr j) x k) =
+      .query j x (fun y => close (k y)) :=
+  rfl
+
 /-- The end of an execution in which the active party returned `a`: the waiting party `B` is
 activated once more, with `none`, and closed. -/
 def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
     ProbComp (ExecOutcome α β) :=
   (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a))
 
+/-- The end of an execution closes the waiting party on `none`, and reports `done a b` if it
+returns `b` and `sentAfterEnd` if it sends:
+`endWith a B = (close (B none)).bind fun ob => pure (ob.elim sentAfterEnd (done a))`. -/
+theorem endWith_eq {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
+    endWith a B =
+      (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a)) :=
+  rfl
+
 /-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
 waits for `A`'s first message. After each message the roles swap. A return costs no fuel; when the
 active party returns, the waiting party is activated once more and closed (`endWith`).
@@ -235,8 +293,9 @@ def execT : ℕ → ∀ {M₁ M₂ α β : Type},
 theorem endWithT_ne_outOfFuel {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
     (endWithT a B).AllOutputs fun q => q.1 ≠ .outOfFuel := by
   refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
-  show Option.elim p.1 ExecOutcome.sentAfterEnd (ExecOutcome.done a) ≠ .outOfFuel
-  cases p.1 <;> simp [Option.elim]
+  rcases p with ⟨_ | b, cs⟩ <;>
+    simp only [OracleComp.allOutputs_pure, Option.elim_none, Option.elim_some, ne_eq,
+      reduceCtorEq, not_false_eq_true]
 
 /-- **Trace invariants** (gate 02 round 2, note 5): on every possible run of
 `execT fuel A B`, write `M_A` and `M_B` for the messages delivered to the first and the second
@@ -259,16 +318,16 @@ theorem execT_trace : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁
     refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
     rcases p with ⟨a | mk, cs⟩
     · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
-        ⟨by simp, by simp, fun h => absurd h hq⟩
-    · exact ⟨by simp, by simp, fun _ => by simp⟩
+        OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun h => absurd h hq⟩
+    · exact OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun _ => by simp⟩
   | fuel + 1, _, _, _, _, A, B => by
     refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
     rcases p with ⟨a | mk, cs⟩
     · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
-        ⟨by simp, by simp, fun h => absurd h hq⟩
+        OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun h => absurd h hq⟩
     · refine OracleComp.AllOutputs.bind (execT_trace fuel (B (some mk.1)) mk.2) fun r hr => ?_
       obtain ⟨h1, h2, h3⟩ := hr
-      refine ⟨?_, ?_, fun h => ?_⟩
+      refine OracleComp.allOutputs_pure.2 ⟨?_, ?_, fun h => ?_⟩
       · simp only [List.length_cons]; omega
       · simp only [List.length_cons]; omega
       · have : r.1 = .outOfFuel := by
diff --git a/TCSlib/Cryptography/Games/Simulate.lean b/TCSlib/Cryptography/Games/Simulate.lean
index d8ac0e1d..906ec1ac 100644
--- a/TCSlib/Cryptography/Games/Simulate.lean
+++ b/TCSlib/Cryptography/Games/Simulate.lean
@@ -116,10 +116,23 @@ def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
   fun i x s => (f i x).bind (fun y => .pure (y, s))
 
+/-- A stateless implementation runs `f i x` and keeps the state:
+`ofComp f i x s = (f i x).bind (fun y => .pure (y, s))`. -/
+theorem ofComp_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
+    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) (i : ι) (x : spec.dom i) (s : σ) :
+    ofComp f i x s = (f i x).bind (fun y => .pure (y, s)) :=
+  rfl
+
 /-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
 def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
   ofComp (fun i x => OracleComp.call i x)
 
+/-- Forwarding asks the same oracle the same query and keeps the state:
+`passthrough i x s = .query i x (fun y => .pure (y, s))`. -/
+theorem passthrough_apply {spec : OracleSpec ι} (i : ι) (x : spec.dom i) (s : σ) :
+    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) :=
+  rfl
+
 /-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
 `impl₁`, and `.inr j` by `impl₂`. -/
 def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
@@ -128,6 +141,20 @@ def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec
   | .inl i => impl₁ i
   | .inr j => impl₂ j
 
+/-- Side by side, the oracle `.inl i` is answered by `impl₁`: `sum impl₁ impl₂ (.inl i) x s =
+impl₁ i x s`. -/
+theorem sum_inl {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
+    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (i : ι₁) (x : s₁.dom i)
+    (s : σ) : sum impl₁ impl₂ (.inl i) x s = impl₁ i x s :=
+  rfl
+
+/-- Side by side, the oracle `.inr j` is answered by `impl₂`: `sum impl₁ impl₂ (.inr j) x s =
+impl₂ j x s`. -/
+theorem sum_inr {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
+    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (j : ι₂) (x : s₂.dom j)
+    (s : σ) : sum impl₁ impl₂ (.inr j) x s = impl₂ j x s :=
+  rfl
+
 end QueryImpl
 
 /-! ### Composing implementations -/
@@ -142,6 +169,16 @@ def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
   fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))
 
+/-- The composed implementation simulates `impl₁`'s answer with `impl₂` and regroups the states:
+`impl₂.comp impl₁ i x s =
+(simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))`. -/
+theorem QueryImpl.comp_apply {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
+    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
+    (impl₁ : QueryImpl spec σ₁ spec') (i : ι) (x : spec.dom i) (s : σ₁ × σ₂) :
+    impl₂.comp impl₁ i x s =
+      (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2))) :=
+  rfl
+
 /-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
 with the composed implementation, up to regrouping the states.
 [VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]
@@ -176,6 +213,15 @@ def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
   fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))
 
+/-- The logged implementation answers as `impl` and appends the entry to the log:
+`impl.withLog i x s = (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))`.
+-/
+theorem QueryImpl.withLog_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
+    (impl : QueryImpl spec σ spec') (i : ι) (x : spec.dom i) (s : σ × QueryLog spec) :
+    impl.withLog i x s =
+      (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩]))) :=
+  rfl
+
 /-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
 simulation, whatever the initial log.
 
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean b/TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean
index 875c3264..eae48686 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean
@@ -191,7 +191,8 @@ the `j`-th distinct prefix (0-indexed, in order of first appearance) by
 `G_{x_n}(⋯ G_{x_{i+2}}(z_{x_{i+1}}) ⋯)`, earlier prefixes as in `H_{i+1}` and later
 prefixes as in `H_i`, and outputs what `A` outputs.
 
-*Cost.* One run of `A`; per query at most `n` evaluations of `G`; `q` fresh seeds and
+*Cost*, for `A` bounded by `q` queries (`OracleAdversary.BoundedBy`; the definition itself
+runs any `A`). One run of `A`; per query at most `n` evaluations of `G`; `q` fresh seeds and
 `q` fresh pairs of seeds as coins together with `A`'s coins, which is lazy sampling of
 `R_i` and `R_{i+1}` [Gar26, footnote 9]: no exponential table is sampled; maintaining the
 list of at most `q` distinct prefixes. The indices `i, j` are non-uniform advice
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean b/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
index 35e6a6d9..9c785839 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
@@ -99,6 +99,21 @@ from all the subtrees of a query to the query. Use it as `induction t using Quer
   | Games.OracleComp.pure a => ret a
   | Games.OracleComp.query () x k => query x k fun o => induct ret query (k o)
 
+/-- `induct` computes on a leaf by its leaf case: `induct hret hquery (ret a) = hret a`. -/
+theorem induct_ret {motive : QueryTree I O α → Sort _} (hret : ∀ a, motive (ret a))
+    (hquery : ∀ x k, (∀ o, motive (k o)) → motive (query x k)) (a : α) :
+    induct (motive := motive) hret hquery (ret a) = hret a :=
+  rfl
+
+/-- `induct` computes on a query node by its query case, applied to the inductions on the
+subtrees: `induct hret hquery (query x k) = hquery x k (fun o => induct hret hquery (k o))`. -/
+theorem induct_query {motive : QueryTree I O α → Sort _} (hret : ∀ a, motive (ret a))
+    (hquery : ∀ x k, (∀ o, motive (k o)) → motive (query x k)) (x : I)
+    (k : O → QueryTree I O α) :
+    induct (motive := motive) hret hquery (query x k) =
+      hquery x k fun o => induct (motive := motive) hret hquery (k o) :=
+  rfl
+
 /-- The output of the query tree `t` when every query `x` is answered by `f x`. -/
 def eval (f : I → O) : QueryTree I O α → α
   | ret a => a
@@ -151,6 +166,18 @@ def simulate (π : I → I') (ans : I → O' → O) : QueryTree I O α → Query
   | ret a => ret a
   | query x k => query (π x) (fun o' => simulate π ans (k (ans x o')))
 
+/-- Simulating a leaf leaves it unchanged: `(ret a).simulate π ans = ret a`. -/
+theorem simulate_ret (π : I → I') (ans : I → O' → O) (a : α) :
+    (ret a : QueryTree I O α).simulate π ans = ret a :=
+  rfl
+
+/-- Simulating a query node asks `π x` and continues, on the answer `o'`, with the simulation of
+the subtree for `ans x o'`:
+`(query x k).simulate π ans = query (π x) (fun o' => (k (ans x o')).simulate π ans)`. -/
+theorem simulate_query (π : I → I') (ans : I → O' → O) (x : I) (k : O → QueryTree I O α) :
+    (query x k).simulate π ans = query (π x) (fun o' => (k (ans x o')).simulate π ans) :=
+  rfl
+
 /-- Running the simulated tree against `g` is running the original tree against the
 oracle that answers `x` by `ans x (g (π x))`. -/
 @[simp] theorem eval_simulate (π : I → I') (ans : I → O' → O) (g : I' → O')
@@ -192,4 +219,10 @@ def oracleDist {ρ : Type*} {I O : Type} (A : OracleAdversary ρ I O) :
     (I → O) → ρ → Bool :=
   fun f r => (A r).eval f
 
+/-- The distinguisher of `A` on the oracle `f` and coins `r` is the run of `A r` against `f`:
+`oracleDist A f r = (A r).eval f`. -/
+theorem oracleDist_apply {ρ : Type*} {I O : Type} (A : OracleAdversary ρ I O) (f : I → O)
+    (r : ρ) : oracleDist A f r = (A r).eval f :=
+  rfl
+
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean b/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
index b3170d33..f09a5e55 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
@@ -100,7 +100,8 @@ Theorem 3.3, the outer adversary `B`]. On a challenge `z ∈ V` and coins
 answers the `k`-th distinct query by `W₁ k` if `k < j`, by `z` if `k = j`, and by
 `G (W₀ k)` if `k > j`, and outputs what `A` outputs.
 
-*Cost.* One run of `A`; at most `q` evaluations of `G`; `q` seeds and `q` values of
+*Cost*, for `A` bounded by `q` queries (`OracleAdversary.BoundedBy`; the definition itself
+runs any `A`). One run of `A`; at most `q` evaluations of `G`; `q` seeds and `q` values of
 fresh randomness (lazy sampling, [Gar26, footnote 9]: no exponential table is sampled);
 bookkeeping of the list of at most `q` distinct queries (membership and position
 lookups). -/
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 8fdeb8bf..d017706a 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -266,6 +266,11 @@ def View.encode (v : View) : List Bool :=
 function on the complete history. -/
 def Strategy.out (S : Strategy) (v : View) : List Bool := S.next v.x v.z v.r v.received
 
+/-- The output on a view is the next-message function on the view's complete history:
+`S.out v = S.next v.x v.z v.r v.received`. -/
+theorem Strategy.out_eq (S : Strategy) (v : View) : S.out v = S.next v.x v.z v.r v.received :=
+  rfl
+
 /-! ### Protocols -/
 
 /-- A protocol [PS10, §4.4] (Def-114.b): a prover strategy, a verifier strategy, the number of
@@ -327,11 +332,26 @@ def transcriptWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.E
     List (List Bool) × List (List Bool) :=
   exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
 
+/-- The transcript against `P'` is `exec` with all `rounds.eval |x|` moves, on the encoded tapes:
+`π.transcriptWith P' x y z r =
+exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)`. -/
+theorem transcriptWith_eq (π : Protocol) (P' : Strategy) (x y z : List Bool)
+    (r : π.ExecCoins P' x) :
+    π.transcriptWith P' x y z r =
+      exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length) :=
+  rfl
+
 /-- The transcript of the honest execution `P(x, y) ↔ V(x, z)` (Def-115.c). -/
 def transcript (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
     List (List Bool) × List (List Bool) :=
   π.transcriptWith π.P x y z r
 
+/-- The honest transcript is the transcript against the honest prover:
+`π.transcript x y z r = π.transcriptWith π.P x y z r`. -/
+theorem transcript_eq_transcriptWith (π : Protocol) (x y z : List Bool)
+    (r : π.ExecCoins π.P x) : π.transcript x y z r = π.transcriptWith π.P x y z r :=
+  rfl
+
 /-- The verifier's output in `P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `out_V`] (Def-115.d):
 `V.next` on the complete history.
 
@@ -340,20 +360,46 @@ last message it sent (`outV_eq_getLast_of_moverIsV`); see `Protocol`. -/
 def outV (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : List Bool :=
   π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
 
+/-- The verifier's output against `P'` is `V.next` on the messages it received:
+`π.outV P' x y z r = π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2`. -/
+theorem outV_eq (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
+    π.outV P' x y z r = π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2 :=
+  rfl
+
 /-- The honest prover's output in `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` (Def-115.d). -/
 def outP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : List Bool :=
   π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1
 
+/-- The honest prover's output is `P.next` on the messages it received:
+`π.outP x y z r = π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1`. -/
+theorem outP_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
+    π.outP x y z r = π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1 :=
+  rfl
+
 /-- The honest verifier's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_V`]
 (Def-115.b). -/
 def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
   ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
 
+/-- The honest verifier's view consists of `x`, its auxiliary input `z`, its tape and the
+messages it received: `π.viewV x y z r = ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩`.
+-/
+theorem viewV_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
+    π.viewV x y z r = ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩ :=
+  rfl
+
 /-- The honest prover's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_P`]
 (Def-115.b). -/
 def viewP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
   ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩
 
+/-- The honest prover's view consists of `x`, its auxiliary input `y`, its tape and the
+messages it received: `π.viewP x y z r = ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩`.
+-/
+theorem viewP_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
+    π.viewP x y z r = ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩ :=
+  rfl
+
 /-- The execution `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` as the pair of views (the joint view)
 [PS10, §4.4] (Def-115.a). -/
 def execution (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View × View :=

## ===== evidence-r2/changed-files.txt =====

TCSlib/Cryptography/Asymptotic/MultiMessage.lean
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
TCSlib/Cryptography/Asymptotic/PRF.lean
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean
TCSlib/Cryptography/Foundations/Experiments.lean
TCSlib/Cryptography/Foundations/Probability.lean
TCSlib/Cryptography/Games/Advantage.lean
TCSlib/Cryptography/Games/BitCodec.lean
TCSlib/Cryptography/Games/Bridges.lean
TCSlib/Cryptography/Games/Bridges/Experiments.lean
TCSlib/Cryptography/Games/Bridges/Machines.lean
TCSlib/Cryptography/Games/Bridges/QueryTree.lean
TCSlib/Cryptography/Games/Bridges/Strategies.lean
TCSlib/Cryptography/Games/Efficiency.lean
TCSlib/Cryptography/Games/Hopping.lean
TCSlib/Cryptography/Games/Machines.lean
TCSlib/Cryptography/Games/OracleComp.lean
TCSlib/Cryptography/Games/Protocols.lean
TCSlib/Cryptography/Games/Simulate.lean
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean

## ===== TCSlib/Cryptography/Asymptotic/MultiMessage.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRF
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Asymptotic.MultiMessageLemmas
import Mathlib.Data.Nat.Choose.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-message secure encryption from a pseudorandom function

The material of [PS10, §3.9]: the many-message encryption scheme
`Gen(1^n): k ← U_n`, `Enc_k(m): r ← U_n, output (r, m ⊕ f_k(r))`, `Dec_k((r, c)) = c ⊕ f_k(r)`
for a pseudorandom function family `{f_k}` [PS10, Algorithm 99.1], and the theorem that it is
multi-message secure [PS10, Theorem 99.2] by the six-hybrid argument: replace `f_k` by a random
function `R` (the PRF property, hybrids `H¹ → H²` and `H⁵ → H⁶`), replace the values `R(r_j)` at
the `q + 1` sampled points by independent uniform pads (identical unless two points collide,
hybrids `H² → H³` and `H⁴ → H⁵`), and use the perfect secrecy of the one-time pad
(`H³ = H⁴`).

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer
(one `n`, samplers and adversaries as functions of uniform coins) is new: the hybrid samplers
`prfEncReal`/`otpEnc`, the oracle adversary `multiMsgAdv` with its chain of `q + 1` queries
(Thm-99.2.1), the collision bound (Thm-99.2.2) and the vector one-time pad (Thm-99.2.3),
assembled into the exact bound `distAdv_prfEncReal_le`. The *asymptotic* layer is the scheme
`prfScheme` as a `PrivateKeyScheme` (its three machines built from a polynomial-time evaluator
of the PRF) and [PS10, Theorem 99.2] over `Complexity.NUPPT`. The proof infrastructure (the
coupling bound, the pair count, the block structure of encoded histories and the next-query
machine of Thm-99.2.1) lives in `TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean`
(namespace `TCSlib.Cryptography.MultiMsg`).

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`.

## Main definitions

* `TCSlib.Cryptography.chainTree` — the query tree asking a fixed tuple of queries.
* `TCSlib.Cryptography.prfEncReal`, `TCSlib.Cryptography.otpEnc` — the hybrid samplers
  `(r_j, m_j ⊕ F(r_j))_j` and `(r_j, m_j ⊕ p_j)_j` of [PS10, Theorem 99.2, proof].
* `TCSlib.Cryptography.multiMsgAdv` — the oracle adversary with `q + 1` queries built from a
  distinguisher of ciphertext tuples (Thm-99.2.1).
* `TCSlib.Cryptography.prfEncFun`, `prfDecFun`, `prfScheme` — the scheme of
  [PS10, Algorithm 99.1].

## Main results

* `TCSlib.Cryptography.prfAdv_multiMsgAdv` — `H¹ → H²` is exactly a PRF advantage (Thm-99.2.1).
* `TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le` — `H² → H³` is bounded by the
  collision probability `C(q+1, 2) 2^{−n}` (Thm-99.2.2).
* `TCSlib.Cryptography.acceptProb_otpEnc` — `H³ = H⁴` by the vector one-time pad (Thm-99.2.3).
* `TCSlib.Cryptography.distAdv_prfEncReal_le` — the exact six-hybrid bound of
  [PS10, Theorem 99.2], concrete.
* `TCSlib.Cryptography.prfScheme_multiEncDist` — the ciphertext tuple of Algorithm 99.1 is the
  encoding of `prfEncReal`.
* `TCSlib.Cryptography.prfScheme_multiMessageSecure` — [PS10, Theorem 99.2].
* `TCSlib.Cryptography.exists_multiMessageSecure_of_prf`,
  `exists_multiMessageSecure_of_exists_prg` — multi-message secure encryption exists if a PRF,
  hence if a PRG, exists.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.9: Algorithm 99.1, Theorem 99.2; §3.7: Definition 93.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries, `prfAdv`).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Query chains -/

/-- The query tree that asks the fixed tuple of queries `xs : Fin k → I` in order and then
outputs `f` applied to the tuple of answers: `k` `query` nodes in a chain. -/
def chainTree {I O α : Type} : ∀ (k : ℕ), (Fin k → I) → ((Fin k → O) → α) → QueryTree I O α
  | 0, _, f => .ret (f Fin.elim0)
  | k + 1, xs, f => .query (xs 0) fun o => chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-- Running a query chain against the oracle `g` outputs `f` of the tuple of answers
`g (xs j)`. -/
theorem eval_chainTree {I O α : Type} (g : I → O) :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α),
      (chainTree k xs f).eval g = f fun j => g (xs j)
  | 0, xs, f => by
    simp only [chainTree, QueryTree.eval_ret]
    congr
    funext j
    exact j.elim0
  | k + 1, xs, f => by
    simp only [chainTree, QueryTree.eval_query]
    rw [eval_chainTree g k]
    congr
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.tail]

/-- A chain of `k` queries makes at most `k` queries. -/
theorem boundedBy_chainTree {I O α : Type} :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α), (chainTree k xs f).BoundedBy k
  | 0, _, _ => trivial
  | k + 1, xs, f => fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-! ### The hybrids of [PS10, Theorem 99.2], concrete -/

section Concrete

variable {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ]

/-- The ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the points
`z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^n`. With `F` the PRF this is the
hybrid `H¹` ("real encryptions"); with `F = randomFunction` (keys are function tables) it is
`H²` ("replace `f` with a truly random function `R`") of [PS10, Theorem 99.2, proof]. -/
def prfEncReal (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

/-- The ciphertext tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with independent uniform pads `p_j`: the
hybrid `H³` ("using OTP") of [PS10, Theorem 99.2, proof]; seeds `(r, p)`. -/
def otpEnc (m : Fin (q + 1) → Fin n → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- **The oracle adversary of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
otherwise (by closure under efficient operations) we contradict the pseudorandomness property"]):
on coins `(r, c)` it queries its oracle at `r₀, …, r_q` (a chain of `q + 1` queries), forms the
tuple `(r_j, m_j ⊕ ans_j)_j` and runs the distinguisher `D` on it with coins `c`. The messages
`m` are hard-wired (non-uniform advice in the machine version). -/
def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin n → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    (multiMsgAdv m D).BoundedBy (q + 1) :=
  fun c => boundedBy_chainTree (q + 1) c.1 _

/-- Running `multiMsgAdv m D` with the oracle `F k` (for a uniform key `k`) accepts with the
probability that `D` accepts the hybrid sampler `prfEncReal F m` (reassociation of the seed
space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdv m D)) = acceptProb (prfEncReal F m) D := by
  unfold acceptProb
  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
  congr 1
  funext z
  simp only [oracleDist, multiMsgAdv, eval_chainTree, Equiv.prodAssoc_apply]
  rfl

/-- **Thm-99.2.1: the gap `H¹ → H²` is a PRF advantage.** The advantage of `D` between the real
encryptions `(r_j, m_j ⊕ F_k(r_j))_j` and the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` is exactly the PRF advantage of the `(q+1)`-query oracle adversary
`multiMsgAdv m D` against `F` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdv m D) =
      distAdv (prfEncReal F m) (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D := by
  rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
    acceptProb_oracleDist_multiMsgAdv]

/-- **The collision bound** ([PS10, Theorem 99.2, proof, "`∃ i, j` such that `r_i = r_j`, but this
happens only with probability `C(q,2) · 2^{−n}`"]): `q + 1` uniform `n`-bit points fail to be
pairwise distinct with probability at most `C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** `¬ Injective r ↔ ∃ (i, j) with i < j, r i = r j`; the union bound
`uprob_exists_le` over the `C(q+1, 2)` pairs `i < j` (`Finset.card_filter` of `univ.filter (i < j)`
on `Fin (q+1) × Fin (q+1)`, `Fin.card_filter_lt`/`Nat.choose_two_right`-style counting); for
`i ≠ j` the pair `(r i, r j)` is uniform on `({0,1}^n)²` (`HardcoreBit.pushesUniform_eval_pair`),
so `uprob (r i = r j) = uprob (fun (a, b) => a = b) = 2^n / 4^n = 1 / 2^n`
(`PushesUniform.uprob_eq`, `uprob_eq_card_filter`, `Fintype.card_fun`, `Fintype.card_bool`). -/
theorem uprob_not_injective_le :
    uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  set S : Finset (Fin (q + 1) × Fin (q + 1)) := univ.filter fun p => p.1 < p.2 with hS
  -- a collision is a pair `i < j` with `r i = r j`
  have h1 : uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      uprob (fun r : Fin (q + 1) → Fin n → Bool => ∃ p ∈ S, r p.1 = r p.2) := by
    refine uprob_mono fun r hr => ?_
    simp only [Function.Injective, not_forall] at hr
    obtain ⟨i, j, hij, hne⟩ := hr
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(i, j), by simp [S, h], hij⟩
    · exact ⟨(j, i), by simp [S, h], hij.symm⟩
  -- each pair `i < j` collides with probability `2^{-n}`
  have h3 : ∀ p ∈ S, uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) = 1 / 2 ^ n := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [S] using hp
    have h : uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) =
        uprob (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2) :=
      (HardcoreBit.pushesUniform_eval_pair (γ := Fin n → Bool) (ne_of_lt hlt)).uprob_eq
        (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2)
    rw [h, MultiMsg.uprob_eq_pair, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  -- the union bound over the `C(q+1, 2)` pairs
  have h2 := uprob_exists_le S (fun p (r : Fin (q + 1) → Fin n → Bool) => r p.1 = r p.2)
  rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hS,
    MultiMsg.card_filter_lt_pairs, mul_one_div] at h2
  exact h1.trans h2

/-- **A uniform table read at distinct points is uniform**: for an injective tuple of points
`r : Fin (q+1) → I`, the map `R ↦ (R (r j))_j` pushes the uniform distribution on tables
`I → O` forward to the uniform distribution on `Fin (q+1) → O` (the generalization of
`HardcoreBit.pushesUniform_eval_pair` from two points to `q + 1` points).

**Proof sketch.** Every fibre of `R ↦ R ∘ r` has the same size `|O|^{|I| − (q+1)}` (the values
off the image of `r` are free, `Equiv.funSplitAt`-style splitting of `I` into the image of `r`
and its complement, `Fintype.card_fun`), so `pushesUniform_of_card_fiber` applies; alternatively
by induction on `q` with `uprob_update_absorb`. -/
theorem pushesUniform_comp_injective {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    {r : Fin (q + 1) → I} (hr : Function.Injective r) :
    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · -- no tables and no tuples: both averages are over empty types
    intro F
    haveI : IsEmpty (I → O) := ⟨fun R => hO.false (R (r 0))⟩
    haveI : IsEmpty (Fin (q + 1) → O) := ⟨fun f => hO.false (f 0)⟩
    simp only [uexp, univ_eq_empty, sum_empty, zero_div]
  · -- split `I` into the image of `r` and its complement: `R ↦ R ∘ r` is a projection
    let e₁ : Fin (q + 1) ⊕ ((Set.range r)ᶜ : Set I) ≃ I :=
      (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range r))
    let e : (I → O) ≃ (Fin (q + 1) → O) × (((Set.range r)ᶜ : Set I) → O) :=
      (Equiv.arrowCongr e₁.symm (Equiv.refl O)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
    have he : (fun R : I → O => fun j => R (r j)) = fun R => (e R).1 := by
      funext R j
      simp [e, e₁]
    rw [he]
    exact (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst

/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
`C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Write both acceptance probabilities as averages over the points `r`
(`uprob_prod` after `uprob_prod_comm`): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform
(`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`; otherwise
`|a(r) − b(r)| ≤ 1` (`uprob_nonneg`, `uprob_le_one`). Hence
`|E_r a − E_r b| ≤ E_r |a − b| ≤ E_r [¬ Injective r] = uprob (¬ Injective)` (`uexp` is monotone
and `|∑| ≤ ∑ |·|`, `uprob_eq_uexp_ite`), and `uprob_not_injective_le` bounds the last term. -/
theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  -- the acceptance probabilities conditioned on the points `r`
  let a : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : ((Fin n → Bool) → (Fin n → Bool)) × ρ =>
      D (fun j => (r j, m j + w.1 (r j))) w.2 = true
  let b : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
  have ha : acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D =
      uexp a :=
    (uprob_comp_equiv ((Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      ((Fin n → Bool) → (Fin n → Bool)) ρ).symm.trans
        ((Equiv.prodComm _ _).prodCongr (Equiv.refl ρ))) _).symm.trans (by rw [uprob_prod]; rfl)
  have hb : acceptProb (otpEnc m) D = uexp b :=
    (uprob_comp_equiv (Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      (Fin (q + 1) → Fin n → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
  -- at injective points the table values are fresh uniform pads
  have hab : ∀ r : Fin (q + 1) → Fin n → Bool, Function.Injective r → a r = b r := by
    intro r hr
    exact ((pushesUniform_comp_injective (O := Fin n → Bool) hr).prodMap
      (HardcoreBit.pushesUniform_id (Ω := ρ))).uprob_eq
      (fun v : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
  rw [distAdv, ha, hb]
  exact (MultiMsg.abs_uexp_sub_le_uprob a b (fun r => ¬ Function.Injective r)
    (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩)
    (fun r hr => hab r (not_not.mp hr))).trans uprob_not_injective_le

/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
same probability.

**Proof sketch.** The map `(r, p) ↦ (r, p ⊕ (m ⊕ m'))` is a bijection of the seed space
(`Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))`) carrying the sampler for `m'` to the
sampler for `m` (in the Boolean group `x + x = 0`); relabel by it (`acceptProb_comp_equiv`). -/
theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool),
      otpEnc m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) = otpEnc m z := by
    intro z
    funext j
    simp only [otpEnc, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst,
      Prod.map_snd, id_eq, Pi.add_apply]
    refine Prod.ext rfl ?_
    funext i
    simp only [Pi.add_apply]
    cases m j i <;> cases m' j i <;> cases z.2 j i <;> rfl
  calc acceptProb (otpEnc m) D
      = acceptProb (fun z => otpEnc m'
          ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z)) D := by
        congr 1
        funext z
        exact (key z).symm
    _ = acceptProb (otpEnc m') D := acceptProb_comp_equiv _ (otpEnc m') D

/-- **[PS10, Theorem 99.2], concrete form: the six-hybrid bound.** For a keyed family
`F : K → {0,1}^n → {0,1}^n`, message vectors `m, m' ∈ ({0,1}^n)^{q+1}` and any distinguisher
`D` of ciphertext tuples, the advantage of `D` between the real encryptions of `m` and of `m'`
is at most `prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) / 2^n`, where `A_m D` is the
`(q+1)`-query oracle adversary `multiMsgAdv m D`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Hybrids `H¹ = prfEncReal F m`, `H² = prfEncReal R m`, `H³ = otpEnc m`,
`H⁴ = otpEnc m'`, `H⁵ = prfEncReal R m'`, `H⁶ = prfEncReal F m'`: `|H¹ − H²|` and `|H⁵ − H⁶|` are
the two PRF advantages (`prfAdv_multiMsgAdv`), `|H² − H³|` and `|H⁴ − H⁵|` are at most the
collision bound (`distAdv_prfEncReal_random_otp_le`), `H³ = H⁴` (`acceptProb_otpEnc`); the
triangle inequality (`abs_sub_le`, five times) finishes. -/
theorem distAdv_prfEncReal_le (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal F m) (prfEncReal F m') D ≤
      prfAdv F (multiMsgAdv m D) + prfAdv F (multiMsgAdv m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  have h12 := prfAdv_multiMsgAdv F m D
  have h56 := prfAdv_multiMsgAdv F m' D
  have h23 := distAdv_prfEncReal_random_otp_le m D
  have h45 := distAdv_prfEncReal_random_otp_le m' D
  have h34 := acceptProb_otpEnc m m' D
  simp only [distAdv] at h12 h56 h23 h45 ⊢
  rw [h12, h56, abs_sub_comm (acceptProb (prfEncReal F m') D)]
  rw [abs_sub_comm (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)]
    at h45
  have t1 := abs_sub_le (acceptProb (prfEncReal F m) D)
    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
    (acceptProb (prfEncReal F m') D)
  have t2 := abs_sub_le (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
    (acceptProb (otpEnc m) D) (acceptProb (prfEncReal F m') D)
  have t3 := abs_sub_le (acceptProb (otpEnc m') D)
    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)
    (acceptProb (prfEncReal F m') D)
  rw [← h34] at t3 h45
  linarith

end Concrete

/-! ### The scheme of [PS10, Algorithm 99.1] -/

/-- The raw string function of `Enc` of [PS10, Algorithm 99.1]: on the machine layout
`⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output the pair `⟨r, w ⊕ E(⟨k, r⟩)⟩`, where `E` evaluates the PRF on
`⟨key, input⟩` and the coin string `r` is the fresh point. -/
def prfEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (List.zipWith xor (pairSndD (NUPPT.inArg z))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (NUPPT.inCoins z))))

/-- Whether the ciphertext `⟨r, c⟩` of the layout `⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` has `n`-bit
components: the domain of `Dec` in [PS10, Algorithm 99.1]. -/
def prfDecWF (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairSndD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length)

/-- The raw string function of `Dec` of [PS10, Algorithm 99.1]: on the layout
`⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` with `n`-bit `r` and `c`, output `c ⊕ E(⟨k, r⟩)`; on any other
ciphertext, output `⊥`, here the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

The source defines `Dec` on pairs of `n`-bit strings only. The guard matters under
chosen-ciphertext attacks: `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, so without it a
malformed ciphertext would evaluate `E` where it is unconstrained, and there it may reveal the
key. -/
def prfDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if prfDecWF z then
    List.zipWith xor (pairSndD (pairSndD (NUPPT.inArg z)))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- `prfEncFun E` is polynomial-time when `E` is: projections, one evaluation of `E`, one
bitwise exclusive-or (`Complexity.polyTimeComputable_pairXor`) and one pairing. -/
theorem polyTimeComputable_prfEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfEncFun E) := by
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode
    (polyTimeComputable_pairXor.comp
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins))))
  convert h using 1
  funext z
  simp [prfEncFun, Function.comp]

/-- The well-formedness test of `Dec` is polynomial-time: two length comparisons
(`Complexity.polyTimeComputable_lenEq`). -/
theorem polyTimeComputable_prfDecWF : PolyTimeComputable (fun z => [prfDecWF z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp]
  exact polyTimeComputable_and
    (hl _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))
    (hl _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))

/-- `prfDecFun E` is polynomial-time when `E` is: the guard, then the branch of the old `Dec`
(`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_prfDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfDecFun E) := by
  refine polyTimeComputable_ite polyTimeComputable_prfDecWF ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have h := polyTimeComputable_pairXor.comp
    (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          NUPPT.polyTimeComputable_inArg))))
  convert h using 1
  funext z
  simp [prfDecFun, Function.comp]

/-- The activation of the encryption machine on `⟨k, w⟩` with coins `r` is
`⟨r, w ⊕ E(⟨k, r⟩)⟩`. -/
theorem runAt_prfEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).runAt n (pairEncode k w) r =
      pairEncode (List.ofFn r) (List.zipWith xor w (E (pairEncode k (List.ofFn r)))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

/-- The activation of the decryption machine on `⟨k, ⟨r, c⟩⟩` with `n`-bit `r` and `c` is
`c ⊕ E(⟨k, r⟩)`. -/
theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k r c : List Bool) (hr : r.length = n) (hc : c.length = n)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k (pairEncode r c)) r' =
      List.zipWith xor c (E (pairEncode k r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]

/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (coins : PolyExpr) (n : ℕ) (k w : List Bool)
    (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    decodeFin n ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k w) r') = none := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  have hf : prfDecWF (pairEncode (pairEncode (NUPPT.advInput n (pairEncode k w)) [])
      (List.ofFn r')) = false := by
    simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  rw [prfDecFun, hf]
  simp [decodeFin, NUPPT.inParam, NUPPT.advInput]

/-- Masking twice with the same pad (at least as long as the message) is the identity
(private copy of the helper of `Asymptotic/Encryption.lean`). -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The many-message encryption scheme of [PS10, Algorithm 99.1]** for a function family
`F` with polynomial-time evaluator `E` on `⟨s, x⟩`: `Gen(1^n)` outputs a uniform `n`-bit key
`k` (its coin string); `Enc_k(m)` draws `r ← U_n` (its coin string) and outputs
`⟨r, m ⊕ f_k(r)⟩`; `Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` (deterministic, coins `const 0`). Correctness is
`(m ⊕ p) ⊕ p = m` with the `n`-bit pad `p = f_k(r)`.

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`. -/
noncomputable def prfScheme (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn re)) = List.ofFn (F n rg re) := hFE n rg re
    rw [h, runAt_prfDec hE _ _ _ _ _ (by rw [List.length_ofFn]; rfl) (by simp), h,
      zipWith_xor_xor_self _ _ (by simp), decodeFin_ofFn]

/-- The encoding of a tuple of ciphertext pairs `(r_j, c_j)_j` as the string handed to a
distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => rfl
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, encodeList_eq_flatMap l]
    simp [pairEncode]

/-- The encoded ciphertext tuple is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which the next-query machine of `MultiMsg.exists_queryChain_nuppt` produces it). -/
theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTuple, encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **The ciphertext tuple of Algorithm 99.1** is the encoding of the hybrid `H¹`: for the key
`k = r.1` and the points `r.2 j`, `multiEncDist n q m r = encodeTuple (prfEncReal (F n) m r)`. -/
theorem prfScheme_multiEncDist (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    (prfScheme F E hE hFE).multiEncDist n q m r = encodeTuple (prfEncReal (F n) m r) := by
  unfold PrivateKeyScheme.multiEncDist encodeTuple
  congr 1
  congr 1
  funext j
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn (m j))) (r.2 j) = _
  rw [runAt_coinKey, runAt_prfEnc hE]
  have h : E (pairEncode (List.ofFn r.1) (List.ofFn (r.2 j))) = List.ofFn (F n r.1 (r.2 j)) :=
    hFE n r.1 (r.2 j)
  rw [h, zipWith_xor_ofFn_add]
  rfl

/-- **[PS10, Theorem 99.2]: the scheme of Algorithm 99.1 is multi-message secure** when `F` is
a pseudorandom function family.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Fix a non-uniform PPT `D` and a budget polynomial `q`. At each `n` choose a
pair of message vectors `(mⁿ, m'ⁿ)` maximizing
`distAdv (multiEncDist n (q n) m) (multiEncDist n (q n) m') (D.distinguisherL n)` over the finite
type of pairs (`Finset.exists_max_image`; the text: "there exists messages `m̄`, `m̄'` … for
infinitely many `n`", hard-wired as advice). *Concrete step:* by `prfScheme_multiEncDist` both
samplers are `encodeTuple ∘ prfEncReal (F n) mⁿ` resp. `m'ⁿ` on the seed space
`K × (Fin (q n + 1) → {0,1}^n)` (the gen coins are the `n`-bit key and the enc coins the points,
definitionally), so with `Dⁿ v c := D.distinguisherL n (encodeTuple v) c` the sunglass identity
`distAdv_comp` and `distAdv_prfEncReal_le` bound the advantage at `n` by
`prfAdv (F n) (multiMsgAdv mⁿ Dⁿ) + prfAdv (F n) (multiMsgAdv m'ⁿ Dⁿ) + 2 · C(q n + 1, 2) / 2^n`
— the six hybrids `H¹, …, H⁶` of the text. *Machine step* (Thm-99.2.1 as an `NUPPT`): for
`v ∈ {m, m'}` the next-query machine `B_v` has advice `⟨encodeList (ofFn (ofFn ∘ vⁿ)), D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `.add (.mul (.add q (.const 1)) (.add (.mul (.const 2) .var) (.const 2))) D.adv`-style),
coins `(q + 1) · var + D.coins` (`NUPPT.exists_split` with `p := .mul (.add q (.const 1)) .var`: the
first `(q n + 1) n` coins are the points `r₀ … r_{q n}`, read as blocks by
`Complexity.polyTimeComputable_blockMap .var`), and on the encoded history `hist` outputs: if
`|hist| ≤ q n` the query `⟨[false], r_{|hist|}⟩` (history length by `polyTimeComputable_blockMap`
counting, `pairDecode`/`decodeFin` are FP), else the verdict `[true, b]` where `b` is `D`'s
verdict on `encodeTuple (r_j, v_j ⊕ ans_j)_j` (`polyTimeComputable_pairXor` blockwise,
`NUPPT.exists_comp`). By induction on the history, `buildTree` with budget `q n + 1` from `[]`
is the chain `chainTree (q n + 1) r (…)`, i.e.
`B_v.toOracleAdversary n n n (q n + 1) = multiMsgAdv vⁿ Dⁿ` up to the coin bijection
`B_v.Coins n ≃ (Fin (q n + 1) → {0,1}^n) × D.Coins n` (`FunFamily.blocks`, `Fin.appendEquiv`),
so `acceptProb_comp_equiv` gives `prfAdv (F n) (B_v^{(q n + 1)}) = prfAdv (F n) (multiMsgAdv vⁿ Dⁿ)`.
*Asymptotic step:* `hF.negligible_prfAdv B_v (.add q (.const 1))` makes both PRF terms
negligible; the collision term is negligible by `negligible_two_pow_neg` and
`Negligible.mul_pow`/`Negligible.const_mul` with `C(q n + 1, 2) ≤ (q n + 1)^2 ≤ C'(n + 1)^{2d}`
from `PolyExpr.eval_le` (`Nat.choose_le_pow`); `Negligible.add` twice, and by maximality
`ε n := ` this sum bounds the advantage for every `n, m, m'`. -/
theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).MultiMessageSecure := by
  intro D q
  -- the worst message pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n) ≤
          distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
          ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines of Thm-99.2.1 for the two hard-wired message vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n n (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n n (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n m m' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    exact ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
      (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
      ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (m, m')).trans ?_
    -- the concrete step: the ciphertext tuples are `encodeTuple ∘ prfEncReal`
    have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
        (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ =
          fun r => encodeTuple (prfEncReal (F n) m₀ r) :=
      fun m₀ => funext fun r => prfScheme_multiEncDist F E hE hFE n (q.eval n) m₀ r
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdv`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin n → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin n → Bool)) ρ c,
          (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n n (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdv v fun w c => D.distinguisherL n (encodeTuple w) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g w => ?_
      rw [hφ g w.1 w.2, multiMsgAdv, eval_chainTree, NUPPT.distinguisherL, encodeTuple_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁, key, key]
    exact distAdv_prfEncReal_le (F n) (μ n).1 (μ n).2
      (fun w c => D.distinguisherL n (encodeTuple w) c)

/-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
theorem exists_multiMessageSecure_of_prf {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) : ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨E, hE, hFE⟩ := hF.easy
  ⟨prfScheme F E hE hFE, prfScheme_multiMessageSecure F hF E hE hFE⟩

/-- **Multi-message secure private-key encryption exists if a PRG exists** ([PS10, Theorems
97.3 and 99.2] combined): GGM gives a PRF, Algorithm 99.1 gives the scheme. -/
theorem exists_multiMessageSecure_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨_, hF⟩ := exists_prf_of_exists_prg h
  exists_multiMessageSecure_of_prf hF

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRF
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the multi-message encryption theorem

The lemmas behind the proofs of `TCSlib/Cryptography/Asymptotic/MultiMessage.lean`
([PS10, Theorem 99.2]), kept in a sibling file so that the statements file stays short:

* **Probability.** The coupling bound `abs_uexp_sub_le_uprob` ("two `[0,1]`-valued
  functions that agree outside an event `E` have averages within `Pr[E]`"), the count of
  pairs `i < j` in `Fin k × Fin k` (`card_filter_lt_pairs`, the `C(k, 2)` of the birthday
  bound), the probability `1 / |α|` that two independent uniform elements coincide
  (`uprob_eq_pair`), and the negligibility of the collision term `C(q(n)+1, 2) · 2^{−n}`
  (`negligible_choose_div_two_pow`).
* **Strings.** The encoded history `encodeHist` is a concatenation of self-delimited
  chunks (`encodeHist_eq_flatMap`);
  the history of a next-query machine with `n`-bit queries and answers consists of blocks of
  the fixed length `6n + 6` (`histBlock`, `length_histBlock`), which the block map of
  `Complexity.polyTimeComputable_blockMap` reads off (`flatMap_range_blocks`); masking a
  history block with the mask block of a message replaces the recorded answer `y` by
  `m ⊕ y` (`zipWith_xor_histBlock_maskBlock`).
* **Machines.** The next-query machine of Thm-99.2.1 (`exists_queryChain_nuppt`): a
  non-uniform PPT whose query tree with budget `q(n) + 1` asks the `q(n) + 1` points read
  from its coins and outputs the verdict of the given distinguisher `D` on the ciphertext
  tuple `(r_j, m_j ⊕ ans_j)_j`, the messages `m` hard-wired as advice. Its raw functions
  `preFun` (the mask) and `postFun` (the move) are built from the FP calculus and the closure
  catalogue of `TCSlib/Complexity/Randomized/Closure.lean`.
* **Oracle adversaries.** Relabelling the coins of an oracle adversary by a bijection
  preserves its PRF advantage (`prfAdv_congr_equiv`).

## Main definitions

* `TCSlib.Cryptography.MultiMsg.histBlock`, `TCSlib.Cryptography.MultiMsg.maskBlock` — the
  block of a history entry and the mask block of a message.
* `TCSlib.Cryptography.MultiMsg.preFun`, `TCSlib.Cryptography.MultiMsg.postFun` — the raw
  string functions of the next-query machine of Thm-99.2.1.

## Main results

* `TCSlib.Cryptography.MultiMsg.abs_uexp_sub_le_uprob` — the coupling bound.
* `TCSlib.Cryptography.MultiMsg.card_filter_lt_pairs` — `#{(i, j) | i < j} = C(k, 2)`.
* `TCSlib.Cryptography.MultiMsg.negligible_choose_div_two_pow` — the collision term is
  negligible.
* `TCSlib.Cryptography.MultiMsg.flatMap_range_blocks` — the block map on a concatenation of
  equal-length chunks.
* `TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock` — masking a history block.
* `TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt` — the next-query machine of
  Thm-99.2.1 and its query tree.
* `TCSlib.Cryptography.MultiMsg.prfAdv_congr_equiv` — coin relabelling preserves `prfAdv`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.9: Algorithm 99.1, Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries, `prfAdv`).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Probability: coupling, pair counting, the collision term -/

/-- The absolute value of an average is at most the average of the absolute values. -/
theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    |uexp f| ≤ uexp fun ω => |f ω| := by
  unfold uexp
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **The coupling bound**: two `[0,1]`-valued functions on a finite sample space that agree
outside the event `E` have averages at most `Pr[E]` apart (the "two experiments that agree
on an event `E` have advantage `≤ Pr[¬E]`" step of [PS10, Theorem 99.2, proof, `H²` vs `H³`]).

**Proof sketch.** `|E a − E b| = |E (a − b)| ≤ E |a − b|` (`abs_uexp_le_uexp_abs`), and
pointwise `|a − b| ≤ [E]` since the difference vanishes off `E` and is at most `1` on it. -/
theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] (ha : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (heq : ∀ ω, ¬ E ω → a ω = b ω) :
    |uexp a - uexp b| ≤ uprob E := by
  rw [← HardcoreBit.uexp_sub, uprob_eq_uexp]
  refine (abs_uexp_le_uexp_abs _).trans (HardcoreBit.uexp_mono fun ω => ?_)
  by_cases hE : E ω
  · rw [if_pos hE]
    obtain ⟨h1, h2⟩ := ha ω
    obtain ⟨h3, h4⟩ := hb ω
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · rw [if_neg hE, heq ω hE, sub_self, abs_zero]

/-- **Counting the pairs `i < j`**: there are `C(k, 2)` pairs `(i, j)` with `i < j` in
`Fin k × Fin k` (the `C(q(n)+1, 2)` of the birthday bound of [PS10, Theorem 99.2]).

**Proof sketch.** The pairs `i < j` and their swaps partition the off-diagonal of
`Fin k × Fin k`, which has `k² − k` elements (`Finset.offDiag_card`); the swap is injective,
so `2 · #{i < j} = k(k − 1)` and `Nat.choose_two_right` finishes. -/
theorem card_filter_lt_pairs (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2).card = k.choose 2 := by
  set S := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2 with hS
  have hunion : S ∪ S.image Prod.swap = (univ : Finset (Fin k)).offDiag := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, i, h, rfl, rfl⟩
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij hji
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hji
    obtain ⟨a, b, hab, rfl, rfl⟩ := hji
    exact absurd hij (not_lt.2 hab.le)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- Two independent uniform elements of a nonempty finite type coincide with probability
`1 / |α|` (Fubini and `OneWay.uprob_eq_one_div_card`). -/
theorem uprob_eq_pair {α : Type*} [Fintype α] [Nonempty α] :
    uprob (fun z : α × α => z.1 = z.2) = 1 / Fintype.card α := by
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : α => a = b) = 1 / Fintype.card α := by
    intro a
    rw [← OneWay.uprob_eq_one_div_card a]
    exact uprob_congr fun b => eq_comm
  simp_rw [h]
  exact HardcoreBit.uexp_const _

/-- **The collision term is negligible**: `n ↦ C(q(n)+1, 2) / 2^n` is negligible for every
syntactic polynomial `q` ([PS10, Theorem 99.2, proof: the collision probability is
negligible]).

**Proof sketch.** `C(k, 2) ≤ k²` (`Nat.choose_le_pow`) and `q(n) + 1 ≤ (C+1)(n+1)^c ≤
(C+1) 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), so the term is at most a constant times
`n^{2c} · 2^{−n}`, negligible by `negligible_two_pow_neg`, `Negligible.mul_pow` and
`Negligible.const_mul`; conclude with `Negligible.mono`. -/
theorem negligible_choose_div_two_pow (q : PolyExpr) :
    Negligible fun n => (Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n := by
  obtain ⟨C, c, hC⟩ := q.eval_le
  have hν : Negligible fun n =>
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow (2 * c)).const_mul _
  refine hν.mono ⟨1, fun n hn => ?_⟩
  have hnat : Nat.choose (q.eval n + 1) 2 ≤ ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by
    have h1 : q.eval n + 1 ≤ (C + 1) * (n + 1) ^ c := by
      have := hC n
      have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos n)
      nlinarith
    have h2 : (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
    calc Nat.choose (q.eval n + 1) 2 ≤ (q.eval n + 1) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ ((C + 1) * (2 * n) ^ c) ^ 2 :=
          Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) 2
      _ = ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by ring
  have hR : (Nat.choose (q.eval n + 1) 2 : ℝ) ≤
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) := by
    exact_mod_cast hnat
  have hinv : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
  calc (Nat.choose (q.eval n + 1) 2 : ℝ) * (2 : ℝ)⁻¹ ^ n
      ≤ ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hR hinv
    _ = _ := by ring

/-! ### Oracle adversaries: coin relabelling -/

/-- Relabelling the coins of an oracle adversary by a bijection preserves its acceptance
probability against every oracle sampler, provided the two trees agree on every oracle. -/
theorem acceptProb_oracleDist_congr_equiv {σ : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype σ] [Fintype ρ]
    [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
    (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
  unfold acceptProb oracleDist
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, h]

/-- **Coin relabelling preserves the PRF advantage**: oracle adversaries whose trees agree on
every oracle after a bijective relabelling of the coins have the same `prfAdv`. -/
theorem prfAdv_congr_equiv {K : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype ρ] [Fintype ρ'] (F : K → I → O) (A : OracleAdversary ρ I O)
    (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
    (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    prfAdv F A = prfAdv F A' := by
  unfold prfAdv distAdv
  rw [acceptProb_oracleDist_congr_equiv F A A' φ h,
    acceptProb_oracleDist_congr_equiv (randomFunction I O) A A' φ h]

/-! ### Strings: chunked encodings, history blocks, mask blocks -/

/-- The block contributed to an encoded history by one (query, answer) pair of `n`-bit
strings: the self-delimited chunk `⟨⟨x, y⟩, []⟩`. -/
def histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- A history block of `n`-bit strings has length `6n + 6`. -/
theorem length_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (histBlock p).length = 6 * n + 6 := by
  simp only [histBlock, length_pairEncode, List.length_ofFn, List.length_nil]
  omega

/-- The encoded history is the concatenation of its blocks. -/
theorem encodeHist_eq_flatMap {n : ℕ} : ∀ h : List ((Fin n → Bool) × (Fin n → Bool)),
    encodeHist h = h.flatMap histBlock
  | [] => rfl
  | p :: h => by
    show pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) = _
    rw [encodeHist_eq_flatMap h, List.flatMap_cons]
    simp [histBlock, pairEncode]

/-- The syntactic block length `6n + 6` of a history block. -/
def histBlockLen : PolyExpr := .add (.mul (.const 6) .var) (.const 6)

/-- Evaluating the block length. -/
theorem eval_histBlockLen (n : ℕ) : histBlockLen.eval n = 6 * n + 6 := rfl

/-- The length of a concatenation of chunks of a common length `b`. -/
theorem length_flatMap_of_length {α : Type*} (f : α → List Bool) (b : ℕ) :
    ∀ L : List α, (∀ x ∈ L, (f x).length = b) → (L.flatMap f).length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatMap_cons, List.length_append,
      length_flatMap_of_length f b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- **The block map on a concatenation of equal-length chunks**: reading the string
`f x₀ ++ ⋯ ++ f x_{k−1}` (chunks of length `b > 0`) in blocks of length `b` and applying `g` to
each block gives `g (f x₀) ++ ⋯ ++ g (f x_{k−1})` (the function of
`Complexity.polyTimeComputable_blockMap`).

**Proof sketch.** Induction on the list: the string has `k + 1` blocks
(`length_flatMap_of_length`), `List.range_succ_eq_map` splits off block `0`, which is `f x`
(`List.take_left'`), and block `i + 1` of `f x ++ rest` is block `i` of `rest`
(`List.drop_append`). -/
theorem flatMap_range_blocks {α : Type*} (f : α → List Bool) (g : List Bool → List Bool) {b : ℕ}
    (hb : 0 < b) : ∀ L : List α, (∀ x ∈ L, (f x).length = b) →
      (List.range ((L.flatMap f).length / b)).flatMap
          (fun i => g (((L.flatMap f).drop (i * b)).take b)) =
        L.flatMap fun x => g (f x)
  | [], _ => by simp
  | x :: L, h => by
    have hx : (f x).length = b := h x (by simp)
    have hL : ∀ y ∈ L, (f y).length = b := fun y hy => h y (by simp [hy])
    have hlen : ((x :: L).flatMap f).length = (L.length + 1) * b := by
      rw [length_flatMap_of_length f b _ h, List.length_cons]
    rw [hlen, Nat.mul_div_cancel _ hb, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_cons]
    congr 1
    · show g (((f x ++ L.flatMap f).drop (0 * b)).take b) = g (f x)
      rw [Nat.zero_mul, List.drop_zero, List.take_left' hx]
    · show (List.range L.length).flatMap
          (fun i => g (((f x ++ L.flatMap f).drop (i.succ * b)).take b)) = L.flatMap fun y => g (f y)
      rw [← flatMap_range_blocks f g hb L hL, length_flatMap_of_length f b L hL,
        Nat.mul_div_cancel _ hb]
      congr 1
      funext i
      rw [List.drop_append,
        List.drop_of_length_le (by rw [hx]; exact Nat.le_mul_of_pos_left b (Nat.succ_pos i)),
        List.nil_append, show i.succ * b - (f x).length = i * b by
          rw [hx, Nat.succ_mul, Nat.add_sub_cancel]]

/-- A constant block map outputs the unary count of the blocks. -/
theorem flatMap_const_singleton {α : Type*} : ∀ L : List α,
    (L.flatMap fun _ => [true]) = List.replicate L.length true
  | [] => rfl
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_singleton L, List.length_cons, List.replicate_succ]
    rfl

/-- A block map outputting `1^n` per block outputs `1^{k·n}` on `k` blocks. -/
theorem flatMap_const_replicate {α : Type*} (n : ℕ) : ∀ L : List α,
    (L.flatMap fun _ => List.replicate n true) = List.replicate (L.length * n) true
  | [] => by simp
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_replicate n L, List.length_cons, Nat.succ_mul, add_comm,
      List.replicate_add]

/-- The query component of a history block: `pairFstD (pairFstD (histBlock p))` is the query
`p.1`. -/
theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
  simp [histBlock]

/-- The mask block of the message `w`: zeros under the (doubled) query and the separators,
`w` doubled under the (doubled) answer, so that `histBlock (x, y) ⊕ maskBlock w` is the
history block of `(x, w ⊕ y)`. -/
def maskBlock {n : ℕ} (w : Fin n → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- A mask block has the length `6n + 6` of a history block. -/
theorem length_maskBlock {n : ℕ} (w : Fin n → Bool) : (maskBlock w).length = 6 * n + 6 := by
  simp only [maskBlock, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
    List.length_cons, List.length_nil]
  omega

/-- Doubling distributes over concatenation. -/
theorem dbl_append (a b : List Bool) : dbl (a ++ b) = dbl a ++ dbl b :=
  List.flatMap_append

/-- Masking with zeros is the identity. -/
theorem zipWith_xor_replicate_false : ∀ l : List Bool,
    List.zipWith xor l (List.replicate l.length false) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, zipWith_xor_replicate_false l,
      Bool.xor_false]

/-- Exclusive-or commutes with doubling. -/
theorem zipWith_xor_dbl : ∀ a b : List Bool,
    List.zipWith xor (dbl a) (dbl b) = dbl (List.zipWith xor a b)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by
    simp only [dbl_cons, List.zipWith_cons_cons, zipWith_xor_dbl a b]

/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).

**Proof sketch.** `⟨⟨x, y⟩, []⟩ = dbl (dbl x) ++ 0011 ++ dbl y ++ 01`; the mask is
`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these
segments, zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
(`zipWith_xor_dbl`). -/
theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  have hyw : List.zipWith xor (List.ofFn y) (List.ofFn w) = List.ofFn (w + y) := by
    rw [zipWith_xor_ofFn_add, add_comm]
  have h1 : histBlock (x, y) =
      (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]) ++
        (dbl (List.ofFn y) ++ [false, true]) := by
    simp only [histBlock, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc]
    rfl
  have h2 : maskBlock w =
      List.replicate (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]).length false ++
        (dbl (List.ofFn w) ++ [false, false]) := by
    simp only [maskBlock, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
      List.length_nil, List.append_assoc]
    congr 2
    omega
  rw [h1, h2, List.zipWith_append (List.length_replicate ..).symm, zipWith_xor_replicate_false,
    List.zipWith_append (by simp only [length_dbl, List.length_ofFn]), zipWith_xor_dbl, hyw]
  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc]
  rfl

/-- The exclusive-or of two concatenations of `k` chunks of pairwise equal lengths is the
concatenation of the chunkwise exclusive-ors. -/
theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
    (∀ j, (F j).length = (G j).length) →
      List.zipWith xor (List.ofFn F).flatten (List.ofFn G).flatten =
        (List.ofFn fun j => List.zipWith xor (F j) (G j)).flatten
  | 0, _, _, _ => rfl
  | k + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons,
      List.flatten_cons, List.zipWith_append (h 0),
      zipWith_xor_flatten_ofFn (fun j => F j.succ) (fun j => G j.succ) fun j => h j.succ]

/-- A string of `q·s` bits read as `q` chunks of `s` bits: chunk `i` is block `i` of
`FunFamily.blocks` (a public duplicate of `EnsembleLemmas.take_drop_ofFn_blocks` in
`Asymptotic/EnsemblesLemmas.lean`). -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) := by
  have hle : i * s + s ≤ q * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s hi
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    show w _ = w (finProdFinEquiv (⟨i, hi⟩, _))
    congr 1
    ext
    simp [finProdFinEquiv]
    ring

/-! ### The next-query machine of Thm-99.2.1 -/

/-- The function of `Complexity.polyTimeComputable_blockMap`: on `⟨u, s⟩`, apply `g` to the
consecutive blocks of `s` of length `b(|u|)` and concatenate. -/
def blockMapFun (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
    g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))

/-- The block map is polynomial-time (`Complexity.polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_blockMapFun (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (blockMapFun b g) :=
  polyTimeComputable_blockMap b hg

/-- The typed head cut `⟨u, s⟩ ↦ s.take (p(|u|))` (`Complexity.polyTimeComputable_pairTakePoly`). -/
def takePolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).take (p.eval (pairFstD z).length)

/-- The typed tail cut `⟨u, s⟩ ↦ s.drop (p(|u|))` (`Complexity.polyTimeComputable_pairDropPoly`). -/
def dropPolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).drop (p.eval (pairFstD z).length)

/-- **The pre-processing of the next-query machine**: on `⟨⟨H, ρ⟩, ⟨M, u⟩⟩` output `H ⊕ M`,
the encoded history masked by the hard-wired mask of the messages (which turns the recorded
answers `ans_j` into `m_j ⊕ ans_j`, `zipWith_xor_histBlock_maskBlock`). -/
def preFun (y : List Bool) : List Bool :=
  List.zipWith xor (pairFstD (pairFstD y)) (pairFstD (pairSndD y))

/-- `preFun` is polynomial-time (`Complexity.polyTimeComputable_pairXor` on two projections). -/
theorem polyTimeComputable_preFun : PolyTimeComputable preFun := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext y
  simp [preFun, Function.comp]

/-- The history slot of the post-processor's argument `⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩`. -/
def postHist (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The points slot `ρ` of the post-processor's argument. -/
def postPoints (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The budget slot `u = 1^{q+1}` of the post-processor's argument. -/
def postBudget (z : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (NUPPT.inArg z)))

/-- The slot `a` of the post-processor's argument holding the distinguisher's output. -/
def postAns (z : List Bool) : List Bool := pairSndD (NUPPT.inArg z)

/-- The unary count `1^k` of the history blocks (block map with the constant `[true]`). -/
def postCount (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))

/-- The unary offset `1^{k·n}` of the next point in the coin string (block map emitting
`1^{|x|}` for the query `x` of each block). -/
def postOffset (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
    (pairEncode (NUPPT.inParam z) (postHist z))

/-- The query move `⟨[false], ρ_k⟩`: the `n`-bit block of the points after the first `k·n`. -/
def postQuery (z : List Bool) : List Bool :=
  pairEncode [false] (takePolyFun .var
    (pairEncode (NUPPT.inParam z) (dropPolyFun .var (pairEncode (postOffset z) (postPoints z)))))

/-- The verdict move `[true, b]` with `b` the distinguisher's acceptance `a = [true]`. -/
def postVerdict (z : List Bool) : List Bool :=
  [true] ++ [decide (pairFstD (pairEncode (postAns z) [true]) = pairSndD (pairEncode (postAns z) [true]))]

/-- **The post-processing of the next-query machine** on the raw layout
`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
`k` the number of history blocks. -/
def postFun (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
  else postQuery z

/-- `postFun` is polynomial-time.

**Proof sketch.** Projections of the layout (`NUPPT.polyTimeComputable_inArg`,
`polyTimeComputable_pairFstD`/`pairSndD`), two block maps
(`Complexity.polyTimeComputable_blockMap`), the typed cuts
(`polyTimeComputable_pairTakePoly`/`pairDropPoly`), a length test
(`Complexity.StateLoop.lenLe_comp`), an equality test (`Complexity.polyTimeComputable_pairEq`)
and one branch (`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_postFun : PolyTimeComputable postFun := by
  have hArg := NUPPT.polyTimeComputable_inArg
  have hParam := NUPPT.polyTimeComputable_inParam
  have hHist : PolyTimeComputable postHist :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hPoints : PolyTimeComputable postPoints :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hBudget : PolyTimeComputable postBudget :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hAns : PolyTimeComputable postAns := polyTimeComputable_pairSndD.comp hArg
  have hCount : PolyTimeComputable postCount :=
    (polyTimeComputable_blockMapFun histBlockLen (polyTimeComputable_const [true])).comp
      (hParam.pairEncode hHist)
  have hOffset : PolyTimeComputable postOffset :=
    (polyTimeComputable_blockMapFun histBlockLen
      (polyTimeComputable_unary.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))).comp
      (hParam.pairEncode hHist)
  have hQuery : PolyTimeComputable postQuery :=
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_pairTakePoly .var).comp
      (hParam.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
        (hOffset.pairEncode hPoints))))
  have hVerdict : PolyTimeComputable postVerdict :=
    (polyTimeComputable_prepend [true]).comp
      (polyTimeComputable_pairEq.comp (hAns.pairEncode (polyTimeComputable_const [true])))
  exact polyTimeComputable_ite (StateLoop.lenLe_comp hCount hBudget) hVerdict hQuery

/-- The mask of a message vector: the concatenation of the mask blocks of its entries. -/
def maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) : List Bool :=
  (List.ofFn fun j => maskBlock (v j)).flatten

/-- The length of a concatenation of strings of a common length `b`. -/
theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
    (∀ x ∈ L, x.length = b) → L.flatten.length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append,
      length_flatten_of_length b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- The length of the mask of `k` messages of `n` bits is `k (6n + 6)`. -/
theorem length_maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) :
    (maskOf v).length = k * (6 * n + 6) := by
  unfold maskOf
  rw [length_flatten_of_length (6 * n + 6), List.length_ofFn]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
  exact length_maskBlock _

/-- The advice bound of the next-query machine: `|⟨mask, 1^{q+1}⟩|`. -/
def adviceBound (q : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) histBlockLen)) (.const 2)) (.add q (.const 1))

/-- Decoding the well-formed query move `⟨[false], x⟩`. -/
theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
    decodeOracleMove ℓ (pairEncode [false] (List.ofFn x)) = .query x := by
  simp [decodeOracleMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- Decoding the verdict move `[true, b]`. -/
theorem decodeOracleMove_ret (ℓ : ℕ) (b : Bool) : decodeOracleMove ℓ [true, b] = .ret b := by
  cases b <;> rfl

/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The projections of the layout read the slots; the two block maps on
`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMap`,
`flatMap_range_blocks` with blocks of length `6n + 6`, `flatMap_const_singleton`,
`flatMap_const_replicate`); the typed cuts then select the block. -/
theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
    (P M u a : List Bool) :
    postFun (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  set z := NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] [] with hz
  have harg : NUPPT.inArg z = pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
    NUPPT.inArg_layout _ _ _ _
  have hpar : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hblocks : ∀ x ∈ hist, (histBlock x).length = 6 * n + 6 := fun x _ => length_histBlock x
  have hpos : 0 < 6 * n + 6 := by omega
  have hcount : postCount z = List.replicate hist.length true := by
    simp only [postCount, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
    exact (flatMap_range_blocks histBlock (fun _ => [true]) hpos hist hblocks).trans
      (flatMap_const_singleton hist)
  have hoffset : postOffset z = List.replicate (hist.length * n) true := by
    simp only [postOffset, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
    refine (flatMap_range_blocks histBlock
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist hblocks).trans ?_
    show hist.flatMap (fun x => List.replicate (pairFstD (pairFstD (histBlock x))).length true) = _
    simp only [pairFstD_pairFstD_histBlock, List.length_ofFn]
    exact flatMap_const_replicate n hist
  have hbudget : postBudget z = u := by
    simp only [postBudget, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : postAns z = a := by
    simp only [postAns, harg, pairSndD_pairEncode]
  have hpoints : postPoints z = P := by
    simp only [postPoints, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  simp only [postFun, hbudget, hcount, List.length_replicate]
  by_cases h : u.length ≤ hist.length
  · rw [if_pos (by simpa using h), if_pos h]
    simp only [postVerdict, hans, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  · rw [if_neg (by simpa using h), if_neg h]
    simp only [postQuery, takePolyFun, dropPolyFun, hoffset, hpoints, hpar, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]

/-- Concatenating the chunks `f (F i)` of a tuple: `flatMap` over `ofFn`. -/
theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List Bool) :
    (List.ofFn F).flatMap f = (List.ofFn fun i => f (F i)).flatten := by
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- **Masking the canonical history**: the pre-processor on the encoded history
`((ρ_j, g ρ_j))_j` with the mask of `v` outputs the encoded ciphertext tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j` (`zipWith_xor_flatten_ofFn`, `zipWith_xor_histBlock_maskBlock`). -/
theorem preFun_encodeHist {n k : ℕ} (ρ v : Fin k → Fin n → Bool)
    (g : (Fin n → Bool) → (Fin n → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOf v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMap, maskOf,
    flatMap_ofFn]
  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlock, length_maskBlock]]
  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
    zipWith_xor_histBlock_maskBlock (ρ j) (g (ρ j)) (v j)))

/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
by closure under efficient operations we contradict the pseudorandomness property"]): for a
non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
queries is not part of the statement).

**Proof sketch.** `B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of
`exists_withAdvice` (advice `⟨maskOf (v n), 1^{q(n)+1}⟩`) of `exists_seq` of `D ∘ preFun`
(`exists_comp`) and the uniform machine of `postFun`. On the encoded history `H` of `k`
blocks the post-processor asks `ρ_k` while `k ≤ q(n)` and otherwise outputs `[true, b]` with
`b` the verdict of `D` on `H ⊕ maskOf (v n)` (`postFun_layout`, `take_drop_ofFn_blocks`,
`preFun_encodeHist`). The tree `buildTree` from the empty history is evaluated by induction on
the remaining budget `j` along the canonical history `((ρ_i, g ρ_i))_{i < q(n)+1-j}`. -/
theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
        (c : D.Coins n),
        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) := by
  classical
  have hβ : ∀ n, (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)).length ≤
      (adviceBound q).eval n := by
    intro n
    simp only [length_pairEncode, length_maskOf, List.length_replicate, adviceBound,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, eval_histBlockLen, le_refl]
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ := D.exists_comp polyTimeComputable_preFun polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ :=
    D₁.exists_seq (NUPPT.ofPolyTimeUniform polyTimeComputable_postFun (.const 0))
  obtain ⟨C₂, hC₂c, hC₂⟩ := C.exists_withAdvice
    (fun n => pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)) (adviceBound q) hβ
  obtain ⟨B, hBc, -, hB⟩ := C₂.exists_split (.mul (.add q (.const 1)) .var)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen n = (q.eval n + 1) * n + D.coinLen n := by
    simp only [NUPPT.coinLen, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, Nat.add_zero]
  let φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n :=
    ((FunFamily.blocks (q.eval n + 1) n).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)))
  refine ⟨φ, fun g ρ c => ?_⟩
  set Pstr : List Bool := List.ofFn ((FunFamily.blocks (q.eval n + 1) n).symm ρ) with hPstr
  have hφ : φ (ρ, c) =
      fun i => Fin.append ((FunFamily.blocks (q.eval n + 1) n).symm ρ) c (Fin.cast hlen i) := by
    funext i
    rfl
  have hcoins : List.ofFn (φ (ρ, c)) = Pstr ++ List.ofFn c := by
    rw [hφ, hPstr, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm _).symm
  -- the activation of `B` on an encoded history
  have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen, hD₁c]
  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin n → Bool)),
      B.runAt n (encodeHist hist) (φ (ρ, c)) =
        postFun (NUPPT.layout (List.replicate n true)
          (pairEncode (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))
            (D.runAt n (preFun (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))) c)) [] []) := by
    intro hist
    have hp : (PolyExpr.mul (.add q (.const 1)) .var).eval n = (q.eval n + 1) * n := rfl
    have hPlen : Pstr.length = (q.eval n + 1) * n := by simp [hPstr]
    have hclen : (List.ofFn c).length = D.coinLen n := by simp
    rw [NUPPT.runAt_eq, hcoins, hB, hp, List.take_left' hPlen, List.drop_left' hPlen]
    have hC₂' := hC₂ n (pairEncode (encodeHist hist) Pstr) (List.ofFn c)
    simp only at hC₂'
    rw [hC₂', hC, hD₁len, List.take_of_length_le hclen.le, List.drop_of_length_le hclen.le, hD₁,
      NUPPT.runAtL_ofPolyTimeUniform]
    rfl
  -- the canonical history along the points `ρ` against the oracle `g`
  let ρ' : ℕ → Fin n → Bool := fun i => if h : i < q.eval n + 1 then ρ ⟨i, h⟩ else fun _ => false
  let hist : ℕ → List ((Fin n → Bool) × (Fin n → Bool)) :=
    fun k => List.ofFn fun i : Fin k => (ρ' i, g (ρ' i))
  have hρ' : ∀ (i : ℕ) (hi : i < q.eval n + 1), ρ' i = ρ ⟨i, hi⟩ := fun i hi => dif_pos hi
  have hist_len : ∀ k, (hist k).length = k := fun k => List.length_ofFn
  have hist_succ : ∀ k, hist (k + 1) = hist k ++ [(ρ' k, g (ρ' k))] := by
    intro k
    simp only [hist]
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
  have hist_top : hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
    simp only [hist]
    congr 1
    funext i
    rw [hρ' i i.isLt]
  -- the next-query function of `B`
  set next : List ((Fin n → Bool) × (Fin n → Bool)) → OracleMove n :=
    fun h => decodeOracleMove n (B.runAt n (encodeHist h) (φ (ρ, c))) with hnext
  have hquery : ∀ k (hk : k < q.eval n + 1), next (hist k) = .query (ρ ⟨k, hk⟩) := by
    intro k hk
    simp only [hnext]
    rw [hrun, postFun_layout, hist_len, if_neg (by simp; omega), hPstr,
      take_drop_ofFn_blocks _ k hk, Equiv.apply_symm_apply, decodeOracleMove_query]
  have hret : next (hist (q.eval n + 1)) =
      .ret (decide (D.runAt n (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
          [true])) := by
    simp only [hnext]
    rw [hrun, postFun_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHist,
      decodeOracleMove_ret]
  -- evaluation of the tree by induction on the remaining budget
  have main : ∀ j, j ≤ q.eval n + 1 →
      (buildTree next j (hist (q.eval n + 1 - j))).eval g =
        decide (D.runAt n (List.ofFn fun j =>
          pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
            [true]) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, buildTree, hret]
      rfl
    | succ j ih =>
      intro hj
      have hk : q.eval n + 1 - (j + 1) < q.eval n + 1 := by omega
      rw [buildTree, hquery _ hk, QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
        show q.eval n + 1 - (j + 1) + 1 = q.eval n + 1 - j by omega]
      exact ih (by omega)
  have h0 : hist 0 = [] := rfl
  have := main (q.eval n + 1) le_rfl
  rw [Nat.sub_self, h0] at this
  exact this

end TCSlib.Cryptography.MultiMsg

## ===== TCSlib/Cryptography/Asymptotic/PRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.GGMReduction
import TCSlib.Cryptography.Asymptotic.GGMReductionEval
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Asymptotic.PRFLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle indistinguishability, pseudorandom functions and the GGM construction

The material of [PS10, §3.8]: random functions `RF_n` in their two descriptions (the function
table and the lazily sampled machine, §3.8.1); oracle indistinguishability of ensembles of
distributions over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` against non-uniform PPT oracle
machines [PS10, Definition 96.1]; pseudorandom functions [PS10, Definition 96.2]; and the
Goldreich–Goldwasser–Micali theorem that a pseudorandom generator yields a pseudorandom
function [PS10, Theorem 97.3] through the tree construction
`f_s(b₁ … b_n) = g_{b_n}(⋯ g_{b₁}(s) ⋯)`.

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer is
the frozen Garg development reused verbatim: query trees and oracle adversaries
(`Pseudorandom/Functions/OracleAdversary.lean`), lazy sampling (`LazySampling.lean`), random
functions and the PRF advantage `prfAdv` (`Defs.lean`), the level hybrids, the query
sub-hybrids and the GGM security bound `exists_ggmBits_dist` (`SubHybrids.lean`, `GGM.lean`).
The *asymptotic* layer is the oracle-adversary model of foundation decision D7: an oracle
machine is a *next-query* `Complexity.NUPPT`, activated once per query on the encoded history
of (query, answer) pairs with one random tape per parameter, with an explicit query budget
quantified universally; `Complexity.NUPPT.toOracleAdversary` unfolds it into a concrete
`OracleAdversary` making at most `q` queries. The theorems are (i) the concrete reduction at
each `n`, (ii) a machine built by the closure calculus of `TCSlib/Complexity/Randomized/`,
(iii) negligible-function arithmetic.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries.

**Deviation:** the GGM tree of [PS10, Theorem 97.3] is built from a *length-doubling*
generator `G : {0,1}^n → {0,1}^{2n}`, which the text obtains "without loss of generality"; a
length-doubling generator is not a `PRG` of this library (the stretch `2n` does not exceed `n`
at `n = 0`), so it is the separate predicate `DoublingPRG`, and the reduction from an arbitrary
`PRG` is the explicit `PRG.doubling` (truncate to `n + 1` bits, expand by [PS10, Lemma 80.5] to
`2n + 1` bits, truncate to `2n`).

**Deviation:** the level hybrids of the formal proof are indexed `HF⁰ = f_s, …, HFⁿ = RF_n`
(`n` gaps, loss `1/n`) where the text writes `HF¹ = f_s, …, HFⁿ = RF_n`; the query sub-hybrids
are indexed by distinct prefixes in order of first appearance (`SubHybrids.lean`).

Proof infrastructure lives in three sibling files: `TCSlib.Cryptography.Asymptotic.PRFLemmas`
(truncation of a generator, the GGM evaluator `ggmEval`), and
`TCSlib.Cryptography.Asymptotic.GGMReduction` / `GGMReductionEval` (the reduction machine
`GGMRed.ggmRedMachine` of Thm-97.3.3: a state loop hosting `D`'s next-query function with the
lazily sampled tables, and its functional identity with `ggmBitsDist`).

## Main definitions

* `TCSlib.Cryptography.OracleEnsemble` — an ensemble of distributions over functions
  [PS10, Definition 96.1]; `OracleEnsemble.random` — the random functions `RF_n`
  [PS10, §3.8.1]; `OracleEnsemble.keyed` — `{s ← U_n : f_s}`.
* `TCSlib.Cryptography.OracleMove`, `decodeOracleMove`, `encodeHist`, `buildTree`,
  `Complexity.NUPPT.toOracleAdversary` — next-query machines as oracle adversaries (D7).
* `TCSlib.Cryptography.OracleEnsemble.Indist` — oracle indistinguishability
  [PS10, Definition 96.1].
* `TCSlib.Cryptography.PRF` — pseudorandom function families [PS10, Definition 96.2].
* `TCSlib.Cryptography.DoublingPRG`, `PRG.truncate`, `PRG.doubling` — length-doubling
  generators and the reduction from an arbitrary generator (Cor-97.a).
* `TCSlib.Cryptography.ggmPRF` — the GGM family `f_s(b₁ … b_n) = g_{b_n}(⋯ g_{b₁}(s) ⋯)`
  [PS10, Theorem 97.3, construction].

## Main results

* `Complexity.NUPPT.toOracleAdversary_boundedBy` — the unfolded tree makes at most `q` queries.
* `TCSlib.Cryptography.acceptProb_random_eq_lazy` — the table and the lazy descriptions of a
  random function give the same acceptance probabilities (Claim-95.b).
* `TCSlib.Cryptography.OracleEnsemble.Indist.refl`, `.symm`, `.trans`,
  `TCSlib.Cryptography.oracle_hybrid_lemma` — reflexivity, symmetry, transitivity and the
  hybrid lemma for oracle ensembles (Claim-96.b).
* `TCSlib.Cryptography.prfAdv_toOracleAdversary` — the advantage of a next-query machine
  against a keyed family is the concrete `prfAdv`.
* `TCSlib.Cryptography.PRG.Secure.doubling` — every PRG yields a length-doubling PRG
  (Cor-97.a).
* `TCSlib.Cryptography.thm_97_3_1`, `thm_97_3_2`, `exists_ggmBitsDist_nuppt` — the level
  hybrids, the query sub-hybrids and the emulation of a sub-hybrid by a non-uniform PPT.
* `TCSlib.Cryptography.ggmPRF_prf` — the GGM family of a length-doubling PRG is a PRF
  [PS10, Theorem 97.3]; `exists_prf_of_exists_prg` — "if a PRG exists then a PRF exists".

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8: Definitions 96.1, 96.2; Theorem 97.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (Definitions 3.6–3.9, Construction 3.3, Theorem 3.3).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Oracle ensembles and random functions [PS10, §3.8.1, Definition 96.1] -/

/-- An **oracle ensemble** [PS10, Definition 96.1]: for every parameter `n` a probability
distribution over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, given (D6/D7) as the pushforward
of the uniform distribution on a finite seed type `σ n` along a sampler `O n`. For the
random-function ensemble the seed is the function table itself (exponentially long, which is
immaterial at the concrete level); for a keyed family the seed is the key.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- The seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- The sampler: the oracle determined by a seed. -/
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fintype

/-- **The random function ensemble** `RF_n` [PS10, §3.8.1, combinatorial description]: the
uniform distribution on functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, sampled by its function
table (the "long array" of the text; `randomFunction I O = id`). The text's count
`2^{n 2^n}` of random functions is `Fintype.card_fun`. -/
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
  O _ := randomFunction _ _

/-- **A keyed family as an oracle ensemble**: `{s ← U_n : f_s}` for a family
`F n : {0,1}^n → {0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` (the first clause of the pseudorandomness
condition of [PS10, Definition 96.2]); the seed is the `n`-bit key. -/
def OracleEnsemble.keyed {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

/-- Unfolding: the random-function ensemble samples by the identity on tables. -/
@[simp] theorem OracleEnsemble.random_O (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (R : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    (OracleEnsemble.random ℓ₁ ℓ₂).O n R = R := rfl

/-- Unfolding: the keyed ensemble samples by `F n`. -/
@[simp] theorem OracleEnsemble.keyed_O {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (OracleEnsemble.keyed F).O n s = F n s := rfl

/-- **The two descriptions of a random function agree** [PS10, §3.8.1, "both of the above
descriptions of a random function give rise to identical distributions"] (Claim-95.b): for an
oracle adversary making at most `q` queries, the probability of accepting with the function
table `RF_n` as oracle equals the probability of accepting when every *new* query is answered
by a fresh uniform value and repeated queries by the recorded answer (the computational
description, `QueryTree.evalLazy` with `q` fresh values `extendStream W`).

**Proof sketch.** Both sides are averages over the adversary's coins `r` (Fubini,
`uprob_prod` after swapping the factors with `uprob_prod_comm`); for each fixed `r` the two
inner probabilities agree by the concrete lazy-sampling theorem `QueryTree.uprob_evalLazy`
applied to the tree `A r`. -/
theorem acceptProb_random_eq_lazy {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) {q : ℕ}
    (hA : A.BoundedBy q) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (fun W : Fin q → (Fin (ℓ₂.eval n) → Bool) => extendStream W) (lazyDist A) := by
  show uprob (fun z : ((Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) × ρ =>
      (A z.2).eval z.1 = true) =
    uprob (fun z : (Fin q → (Fin (ℓ₂.eval n) → Bool)) × ρ =>
      (A z.2).evalLazy (extendStream z.1) [] = true)
  rw [uprob_prod_comm (fun R (r : ρ) => (A r).eval R = true),
    uprob_prod_comm (fun W (r : ρ) => (A r).evalLazy (extendStream W) [] = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  exact (QueryTree.uprob_evalLazy (· = true) (hA r)).symm

/-! ### Next-query machines as oracle adversaries (D7) -/

/-- A move of a next-query oracle machine: either the next query `x ∈ {0,1}^{ℓ₁}` or the
final verdict `b`. -/
inductive OracleMove (ℓ₁ : ℕ)
  /-- Ask the oracle at `x`. -/
  | query (x : Fin ℓ₁ → Bool)
  /-- Stop with the verdict `b`. -/
  | ret (b : Bool)

/-- Decoding of a machine output as a move: `⟨[false], x⟩` with `x` an `ℓ₁`-bit string is the
query `x`; the two-bit string `[true, b]` is the verdict `b`; any other output is the verdict
`false` (D7: ill-formed outputs count as rejection). -/
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

/-- The encoding of the history of (query, answer) pairs handed to a next-query machine: the
nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The empty history is encoded as the empty string: `encodeHist [] = []`. -/
theorem encodeHist_nil {ℓ₁ ℓ₂ : ℕ} :
    encodeHist ([] : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) = [] :=
  rfl

/-- A history is encoded pair by pair:
`encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h)`. -/
theorem encodeHist_cons {ℓ₁ ℓ₂ : ℕ} (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))
    (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  rfl

/-- The query tree of a next-query function `next` (the machine's move on a history) with the
query budget `q`, started from the history `hist`: a verdict stops; a query within budget
becomes a `query` node whose continuation appends the answer to the history; a query when the
budget is exhausted is the forced verdict `false` (D7). -/
def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

section BuildTree

variable {ℓ₁ ℓ₂ : ℕ} {next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁}
  {hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))}

/-- With the budget spent, a verdict stops the tree: `buildTree next 0 hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_zero_of_ret {b : Bool} (h : next hist = .ret b) :
    buildTree next 0 hist = .ret b := by
  rw [buildTree, h]

/-- With the budget spent, a query gives the forced verdict `false`:
`buildTree next 0 hist = ret false` when `next hist = query x`. -/
theorem buildTree_zero_of_query {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next 0 hist = .ret false := by
  rw [buildTree, h]

/-- Within budget, a verdict stops the tree: `buildTree next (q + 1) hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_succ_of_ret {q : ℕ} {b : Bool} (h : next hist = .ret b) :
    buildTree next (q + 1) hist = .ret b := by
  rw [buildTree, h]

/-- Within budget, a query becomes a query node whose continuation appends the answer:
`buildTree next (q + 1) hist = query x (fun o => buildTree next q (hist ++ [(x, o)]))` when
`next hist = query x`. -/
theorem buildTree_succ_of_query {q : ℕ} {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next (q + 1) hist = .query x (fun o => buildTree next q (hist ++ [(x, o)])) := by
  rw [buildTree, h]

end BuildTree

/-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      (buildTree next q hist).BoundedBy q
  | 0, hist => by
    unfold buildTree
    cases next hist <;> exact trivial
  | q + 1, hist => by
    unfold buildTree
    cases next hist with
    | ret b => exact trivial
    | query x => exact fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
machine `D(1^n, ·)` is run, with one random tape `r` for the whole interaction, on the
encoded history; its output is decoded as a query or a verdict. -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

/-- The tree of `D` on the coins `r` is built from the empty history, the next move being `D`'s
output on the encoded history, decoded:
`D.toOracleAdversary n ℓ₁ ℓ₂ q r =
buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []`. -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_eq (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ)
    (r : D.Coins n) :
    D.toOracleAdversary n ℓ₁ ℓ₂ q r =
      buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q [] :=
  rfl

/-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
Induction on the budget (`buildTree_boundedBy`). -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
  fun _ => buildTree_boundedBy _ q []

/-! ### Oracle indistinguishability [PS10, Definition 96.1] -/

/-- **Oracle indistinguishability** [PS10, Definition 96.1]: `{O_n} ≈ {O'_n}` iff for every
non-uniform PPT oracle machine `D` (a next-query `NUPPT`) and every polynomial query budget
`q`, the function `n ↦ |Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]|` is
negligible, where `D^F(1^n)` is the run of the query tree `D.toOracleAdversary n ℓ₁(n) ℓ₂(n) q(n)`
against `F`. (The text writes `{O'_n} ≈ {O'_n}`, a typo.)

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))

/-- **Reflexivity of oracle indistinguishability** (non-vacuity of
[PS10, Definition 96.1]): every oracle ensemble is indistinguishable from itself, the
advantage being identically `0`. -/
theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  intro D q
  have h : (fun n => distAdv (O.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) = fun _ => 0 := by
    funext n
    simp [distAdv]
  rw [h]
  exact negligible_zero

/-- **Symmetry of oracle indistinguishability**: the advantage is symmetric in the two
ensembles (`abs_sub_comm`). -/
theorem OracleEnsemble.Indist.symm {ℓ₁ ℓ₂ : PolyExpr} {O O' : OracleEnsemble ℓ₁ ℓ₂}
    (h : O.Indist O') : O'.Indist O := by
  intro D q
  have e : (fun n => distAdv (O'.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) =
      fun n => distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := by
    funext n
    exact abs_sub_comm _ _
  rw [e]
  exact h D q

/-- **Transitivity of oracle indistinguishability** (the two-step case of the hybrid lemma
for oracles, [PS10, §3.8.2, "oracle indistinguishability satisfies … the Hybrid Lemma"]): the
advantage between `O` and `O''` is at most the sum of the advantages between `O, O'` and
`O', O''` (triangle inequality `abs_sub_le`), and sums of negligible functions are negligible
(`Negligible.add`, `Negligible.mono`). -/
theorem OracleEnsemble.Indist.trans {ℓ₁ ℓ₂ : PolyExpr} {O O' O'' : OracleEnsemble ℓ₁ ℓ₂}
    (h₁ : O.Indist O') (h₂ : O'.Indist O'') : O.Indist O'' := by
  intro D q
  refine ((h₁ D q).add (h₂ D q)).mono ⟨0, fun n _ => ?_⟩
  have t := abs_sub_le (acceptProb (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))))
    (acceptProb (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))))
    (acceptProb (O''.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))))
  have h0 : 0 ≤ distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) +
      distAdv (O'.O n) (O''.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 : 0 ≤ distAdv (O.O n) (O''.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := abs_nonneg _
  rw [abs_of_nonneg h1, abs_of_nonneg h0]
  exact t

/-- **The hybrid lemma for oracles** [PS10, §3.8.2, "oracle indistinguishability satisfies …
the Hybrid Lemma"] (Claim-96.b), at one parameter: if the oracle adversary `A` distinguishes
the oracle distributions `H 0` and `H m` with advantage `ε`, then it distinguishes some
consecutive pair `H i, H (i+1)` (`i < m`) with advantage at least `ε / m`. This is the
concrete `hybrid_lemma` (`exists_hybrid_gap`) applied to the distinguisher `oracleDist A`. -/
theorem oracle_hybrid_lemma {σ : Type*} {I O : Type} {ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (H : ℕ → σ → (I → O)) (A : OracleAdversary ρ I O) :
    ∃ i < m, distAdv (H 0) (H m) (oracleDist A) / m ≤ distAdv (H i) (H (i + 1)) (oracleDist A) :=
  hybrid_lemma hm H (oracleDist A)

/-! ### Pseudorandom functions [PS10, Definition 96.2] -/

/-- **Pseudorandom function family** [PS10, Definition 96.2]: a family
`{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` given as `F n : {0,1}^n → {0,1}^n → {0,1}^n` (key, input,
output) is pseudorandom iff (1) *easy to compute*: a polynomial-time string function computes
`f_s(x)` from the pair `⟨s, x⟩`; (2) *pseudorandom*: the keyed oracle ensemble `{s ← U_n : f_s}`
is oracle-indistinguishable from the random functions `{F ← RF_n : F}`.

**Deviation:** clause (1) is a deterministic polynomial-time evaluator on `⟨s, x⟩` instead of
a PPT computing `f_s(x)` with probability one (equivalent by `Complexity.NUPPT.Computes` and
`ofPolyTimeUniform`, as for `FunFamily.Easy`); the key length is the parameter `n`
(`{0,1}^{|s|}` with `|s| = n`). -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)

/-- The advantage of the next-query machine `D` with budget `q` between the keyed family `F`
and the random functions is the concrete PRF advantage `prfAdv` of [Gar26, Definition 3.9]
(definitional: `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`). -/
theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
        (oracleDist (D.toOracleAdversary n n n q)) =
      prfAdv (F n) (D.toOracleAdversary n n n q) := rfl

/-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) := by
  have h := hF.pseudorandom D q
  simpa only [prfAdv_toOracleAdversary] using h

/-! ### Length-doubling generators (Cor-97.a) -/

/-- The output ensemble `{s ← U_n : G(s)}` of a length-doubling generator
`G : {0,1}^n → {0,1}^{2n}`, with the stretch `2n` as the syntactic polynomial `2 · var` (D9). -/
def doublingEnsemble (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) :
    Ensemble (.mul (.const 2) .var) where
  σ n := Fin n → Bool
  X := G

/-- **A length-doubling pseudorandom generator** `g : {0,1}^n → {0,1}^{2n}` [PS10, proof of
Theorem 97.3, "let `g` be a length-doubling pseudorandom generator"]: efficiently computable
and with a pseudorandom output ensemble, exactly as `PRG.Secure` [PS10, Definition 77.1] but
with the stretch `2n`.

**Deviation:** a length-doubling generator is not a `PRG` of this library (the expansion
clause `n < 2n` fails at `n = 0`), hence this separate predicate; `PRG.Secure.doubling`
(Cor-97.a) produces one from any `PRG`. -/
structure DoublingPRG (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) : Prop where
  /-- Efficiency: a polynomial-time string function computes `G n s` from the seed string. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)
  /-- Pseudorandomness of the output ensemble [PS10, Definition 74.1]. -/
  pseudorandom : (doublingEnsemble G).Pseudorandom

/-- **Pseudorandomness of a length-doubling generator unfolded**: for every non-uniform PPT
`D` the concrete PRG advantage `prgAdv (G n) (D(1^n, ·))` [Gar26, Definition 3.5] between
`G(U_n)` and `U_{2n}` is negligible (definitional, `Ensemble.pseudorandom_iff_prgAdv`). -/
theorem DoublingPRG.negligible_prgAdv {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    (hG : DoublingPRG G) (D : NUPPT) :
    Negligible fun n => prgAdv (G n) (D.distinguisher n (2 * n)) :=
  (Ensemble.pseudorandom_iff_prgAdv (doublingEnsemble G)).1 hG.pseudorandom D

/-- **Truncation of a generator to `n + 1` bits** (first step of Cor-97.a): the first `n + 1`
output bits of `G n` (the stretch `ℓ(n) > n` makes them available). -/
def PRG.truncate (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
  fun n s i => P.G n s (Fin.castLE (P.expands n) i)

/-- The stretch `2n + 1` used to produce a length-doubling generator from a one-bit-stretch
generator by [PS10, Lemma 80.5]: it exceeds `n` at every `n` (unlike `2n`). -/
theorem two_mul_add_one_expands (n : ℕ) :
    n < (PolyExpr.add (.mul (.const 2) .var) (.const 1)).eval n := by
  show n < 2 * n + 1
  omega

/-- **The length-doubling generator obtained from an arbitrary PRG** (Cor-97.a, the "without
loss of generality" of [PS10, proof of Theorem 97.3]): truncate `G` to `n + 1` bits
(`PRG.truncate`), expand the one-bit-stretch generator to `2n + 1` bits by the construction of
[PS10, Lemma 80.5] (`PRG.expand`), and keep the first `2n` bits. -/
def PRG.doubling (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool) :=
  fun n s i => (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
    two_mul_add_one_expands).G n s (Fin.castLE (Nat.le_succ (2 * n)) i)

/-- Closed form of the length-doubling generator: bit `i` of `P.doubling n s` is the last bit
of the truncated generator applied to the `i`-th iterate of `s ↦ init (G₁(s))` on `s`
(`PRG.expand_G`). -/
theorem PRG.doubling_apply (P : PRG) (n : ℕ) (s : Fin n → Bool) (i : Fin (2 * n)) :
    P.doubling n s i =
      P.truncate n ((fun x => Fin.init (P.truncate n x))^[i] s) (Fin.last n) := rfl

/-- **Truncation preserves pseudorandomness** (first half of Cor-97.a): if `G` is a secure
PRG then its truncation to `n + 1` bits is a secure one-bit-stretch PRG.

**Proof sketch.** *Easy:* the evaluator of `G` followed by `List.take (n + 1)`
(`Complexity.polyTimeComputable_pairTakePoly (.add .var (.const 1))` on `⟨1^n, G(s)⟩`, with
`1^n = replicate |s| true` by `polyTimeComputable_unaryPoly .var`); `List.take` of `ofFn` is
`ofFn` of the restriction (`List.ofFn_castLE`-style, `List.take_ofFn`). *Pseudorandom:* for a
distinguisher `D` of the truncation, the machine `D'` that truncates its `ℓ(n)`-bit input to
`n + 1` bits and runs `D` (`NUPPT.exists_comp` with `pre := pairTakePoly`) satisfies
`prgAdv (G n) (D'.distinguisher n (ℓ n)) = prgAdv (P.truncate n) (D.distinguisher n (n+1))` by
the sunglass identity `distAdv_comp` with the projection `t ↦ t ∘ castLE` (a uniform
`ℓ(n)`-bit string projects to a uniform `(n+1)`-bit string, `uprob_comp_equiv` on
`Fin.appendEquiv`/`Equiv.funSplitAt`), and `PRG.secure_iff` applied to `hP` gives the
negligible bound; `Negligible.mono` with the equality. -/
theorem PRG.Secure.truncate {P : PRG} (hP : P.Secure) : (PRG.oneBit P.truncate).Secure := by
  have hm : ∀ n, (PolyExpr.add .var (.const 1)).eval n ≤ P.stretch.eval n := fun n => P.expands n
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := hP.truncateTo_easy _ hm
    exact ⟨E, hE, fun n s => hEs n s⟩
  · exact hP.truncateTo_negligible _ hm D

/-- **Any PRG yields a length-doubling PRG** (Cor-97.a, [PS10, proof of Theorem 97.3, first
paragraph]): if `G` is a secure PRG then `P.doubling : {0,1}^n → {0,1}^{2n}` is a secure
length-doubling generator.

**Proof sketch.** By `PRG.Secure.truncate` the one-bit-stretch generator `P.truncate` is
secure, so by [PS10, Lemma 80.5] (`prg_expand` with `ℓ := 2 · var + 1`) the expansion to
`2n + 1` bits is a secure `PRG`; `P.doubling` is its truncation to `2n` bits
(`PRG.doubling_apply`, `PRG.expand_G`). *Easy:* the evaluator of the expansion followed by
`List.take (2n)` (`polyTimeComputable_pairTakePoly (.mul (.const 2) .var)`). *Pseudorandom:*
exactly as in `PRG.Secure.truncate`: a distinguisher `D` of `P.doubling` becomes the
distinguisher `D ∘ take (2n)` of the expansion (`NUPPT.exists_comp`), `distAdv_comp` with the
projection `Fin (2n + 1) → Fin (2n)` and `uprob_comp_equiv` identify the advantages, and the
pseudorandomness of the expansion (`PRG.secure_iff`) gives the negligible bound. -/
theorem PRG.Secure.doubling {P : PRG} (hP : P.Secure) : DoublingPRG P.doubling := by
  have hQ : (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
      two_mul_add_one_expands).Secure :=
    prg_expand P.truncate _ two_mul_add_one_expands hP.truncate
  have hm : ∀ n, (PolyExpr.mul (.const 2) .var).eval n ≤
      (PolyExpr.add (.mul (.const 2) .var) (.const 1)).eval n := fun n => Nat.le_succ _
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := hQ.truncateTo_easy _ hm
    exact ⟨E, hE, fun n s => hEs n s⟩
  · exact hQ.truncateTo_negligible _ hm D

/-! ### The GGM construction [PS10, Theorem 97.3] -/

/-- **The GGM family** [PS10, Theorem 97.3, construction] (Constr-97.b): for a length-doubling
generator `g(x) = g₀(x) ‖ g₁(x)`, `f_s(b₁ b₂ … b_n) = g_{b_n}(g_{b_{n−1}}(⋯ (g_{b₁}(s)) ⋯))` —
a walk down a binary tree of height `n` whose root is the seed `s` and whose children of a
node `y` are `g₀(y)` and `g₁(y)`. This is the concrete `ggmBits (G n)` [Gar26, Construction 3.3]
at every parameter. -/
def ggmPRF (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) :
    ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) :=
  fun n => ggmBits (G n)

/-- Unfolding: the GGM family at `n` is `ggmBits (G n)`. -/
@[simp] theorem ggmPRF_apply (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) (n : ℕ) :
    ggmPRF G n = ggmBits (G n) := rfl

/-- **The GGM evaluation is polynomial-time** (Claim-97.c, clause (1) of
[PS10, Definition 96.2] for the GGM family): from a polynomial-time evaluator `E` of the
length-doubling generator, a polynomial-time string function computes `f_s(x)` from `⟨s, x⟩`.

**Proof sketch.** `n` iterations of "evaluate `E` on the current label and keep the half
selected by the next bit of `x`": `Complexity.polyTimeComputable_iterate` with `R := var`
(at most `|⟨s, x⟩|` rounds) on the state word `⟨y, rest⟩` (current label `y`, remaining bits
`rest` of `x`), whose step is `⟨pairSel (head rest) (E y), tail rest⟩` with `pairSel b` the
first or last `|y|` bits (`polyTimeComputable_pairTakePoly`/`pairDropPoly` at `var` on
`⟨1^{|y|}, E y⟩`, `polyTimeComputable_unaryPoly`, `polyTimeComputable_ite` on the head bit,
`Turing.FinTM.computesFunInTime_stripLast`-style head/tail primitives); the orbit is bounded by
`|⟨s, x⟩| + 2` since labels keep length `n`; the output is the label after `|x|` rounds (the
step is the identity once `rest = []`). The functional identity with `ggmBits (G n) s x =
ggmFrom (splitHalves ∘ G n) x 0 s` is proved by induction on the position `i`
(`ggmFrom_of_lt`, `ggmFrom_of_le`, `splitHalves` as take/drop of `ofFn`). -/
theorem exists_ggmPRF_evaluator {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (hG : ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)) :
    ∃ E' : List Bool → List Bool, PolyTimeComputable E' ∧
      ∀ n (s x : Fin n → Bool), E' (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (ggmPRF G n s x) :=
  ⟨ggmEval E, ggmEval_poly hE, fun n s x => ggmEval_ofFn (hG n) s x⟩

/-- **The level hybrids** `HF^i` of [PS10, proof of Theorem 97.3] (Thm-97.3.1): with levels
`0, …, i` of the tree random and the levels below pseudorandom (`hybridOracle`), the hybrid
`HF⁰` is the GGM function with a uniform seed and `HFⁿ` is a uniform random function `RF_n`
(`hybridProb_zero`, `hybridProb_top`).

**Deviation:** the formal indexing is `HF⁰ = f_s, …, HFⁿ = RF_n` (`n` gaps) where the text
writes `HF¹ = f_s, …, HFⁿ = RF_n`. -/
theorem thm_97_3_1 {ρ : Type*} [Fintype ρ] (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool))
    (n : ℕ) (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) :
    hybridProb (splitHalves ∘ G n) A 0 = acceptProb (ggmPRF G n) (oracleDist A) ∧
      hybridProb (splitHalves ∘ G n) A n =
        acceptProb ((OracleEnsemble.random .var .var).O n) (oracleDist A) :=
  ⟨hybridProb_zero _ A, hybridProb_top _ A⟩

/-- **The query sub-hybrids** `HHF^j` of [PS10, proof of Theorem 97.3] (Thm-97.3.2): for an
adversary making at most `q` queries, the gap between the consecutive level hybrids `HF^i` and
`HF^{i+1}` is at most the sum over `j < q` of the PRG advantages of the explicit distinguishers
`B_{i,j} = ggmBitsDist (G n) A q i j` between `G(U_n)` and `U_{2n}` (`hybridProb_level`,
`distAdv_ggmBitsDist`). Together with `exists_ggmBits_dist` this is the text's "`D` can
distinguish `HHF^j` and `HHF^{j+1}` for some `j` with probability `ε/(n p(n))`".

**Deviation:** the sub-hybrids are indexed by *distinct* prefixes in order of first
appearance, the challenge answering every query with the `j`-th distinct prefix. -/
theorem thm_97_3_2 {ρ : Type*} [Fintype ρ] (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool))
    (n : ℕ) (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) {q : ℕ} (hA : A.BoundedBy q)
    (i : Fin n) :
    |hybridProb (splitHalves ∘ G n) A i - hybridProb (splitHalves ∘ G n) A ((i : ℕ) + 1)| ≤
      ∑ j : Fin q, prgAdv (G n) (ggmBitsDist (G n) A q i j) := by
  have h := hybridProb_level (splitHalves ∘ G n) A hA i
  simpa only [prgAdv, distAdv_ggmBitsDist] using h

/-- `decodeOracleMove` in terms of the `Option` form of `TCSlib.Cryptography.GGMRed`: the
query `queryOf` if there is one, else the verdict `verdictOf` (`[true, true]` is the only
accepting output).

**Proof sketch.** Case split along the match of `decodeOracleMove`. A pair `⟨[false], x⟩`
decodes to the query `x` iff `|x| = ℓ₁`, and otherwise to `ret false`, which is `verdictOf` of
a word starting with `false`. The two-bit word `[true, b]` is not a pair and decodes to `ret b`,
which is `verdictOf [true, b]`. Any other word is neither a query nor `[true, true]`. -/
private theorem decodeOracleMove_eq (ℓ₁ : ℕ) (w : List Bool) :
    decodeOracleMove ℓ₁ w =
      match GGMRed.queryOf ℓ₁ w with
      | some x => .query x
      | none => .ret (GGMRed.verdictOf w) := by
  unfold decodeOracleMove
  split
  · rename_i w o w' x hx
    have hw := eq_pairEncode_of_pairDecode w _ _ hx
    have hq : GGMRed.queryOf ℓ₁ w = decodeFin ℓ₁ x := by
      simp only [GGMRed.queryOf, hx]
    rw [hq]
    cases decodeFin ℓ₁ x with
    | some y => rfl
    | none =>
      simp only
      congr 1
      rw [hw]
      simp [GGMRed.verdictOf, pairEncode]
  · rename_i o w' b hp
    have hq : GGMRed.queryOf ℓ₁ [true, b] = none := by cases b <;> rfl
    rw [hq]
    cases b <;> rfl
  · rename_i w o w' hb hp
    have hq : GGMRed.queryOf ℓ₁ w = none := by
      rw [Option.eq_none_iff_forall_ne_some]
      intro x hx
      rw [GGMRed.queryOf_eq_some_iff] at hx
      exact hp (List.ofFn x) hx
    rw [hq]
    simp only [OracleMove.ret.injEq, GGMRed.verdictOf]
    exact (decide_eq_false_iff_not.2 fun h => hb true h).symm

/-- `buildTree` of the decoded moves is `buildTreeQ` of the raw outputs. -/
private theorem buildTree_eq_buildTreeQ {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → List Bool) :
    ∀ (b : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      buildTree (fun h => decodeOracleMove ℓ₁ (next h)) b hist = GGMRed.buildTreeQ next b hist
  | 0, hist => by
    rw [GGMRed.buildTreeQ_zero]
    unfold buildTree
    rw [decodeOracleMove_eq]
    cases GGMRed.queryOf ℓ₁ (next hist) <;> rfl
  | b + 1, hist => by
    rw [GGMRed.buildTreeQ_succ]
    unfold buildTree
    rw [decodeOracleMove_eq]
    cases GGMRed.queryOf ℓ₁ (next hist) with
    | none => rfl
    | some x =>
      simp only
      congr 1
      funext o
      exact buildTree_eq_buildTreeQ next b (hist ++ [(x, o)])

/-- **A sub-hybrid can be emulated by a non-uniform PPT** (Thm-97.3.3, [PS10, proof of
Theorem 97.3, last paragraph]: "queries to `HHF^j` can be emulated in p.p.t. … it follows by
closure under efficient operations that `D` contradicts the pseudorandom property of `g`"):
for a next-query machine `D` with budget `q` and hybrid indices `i, j : ℕ → ℕ` (the
non-uniform advice of the reduction), there is a non-uniform PPT `B` whose PRG advantage
against `G n` is exactly the advantage of the concrete distinguisher
`ggmBitsDist (G n) (D^{(q n)}) (q n) (i n) (j n)` whenever the indices are in range.

**Proof sketch.** `B` has advice `⟨⟨1^{i n}, 1^{j n}⟩, D.advice n⟩` (`NUPPT.exists_withAdvice`
with bound `.add (.add (.mul (.const 2) .var) (.const 2)) q`-style) and coins
`(q · n) + (q · 2n) + D.coins` (`NUPPT.exists_split` twice: the `q n` fresh seeds and the `q n`
fresh pairs of the lazily sampled tables `R_i`, `R_{i+1}`, read as blocks by
`polyTimeComputable_blockMap`). On the challenge `z ∈ {0,1}^{2n}` it hosts `D`'s next-query
function in a `Complexity.polyTimeComputable_iterateFind` loop over at most `q n + 1`
activations: the state word holds the encoded history, the list of distinct `i`-bit prefixes
seen so far (`QueryTree.noteQuery`), and `D`'s single random tape; each round runs `D.output` on
the history (`NUPPT.polyTimeComputable_output`), decodes the move (`decodeOracleMove`:
`pairDecode`/`decodeFin` are FP), and answers a query `x` by walking the lower part of the tree
from the label of its prefix — the `k`-th distinct prefix gets the uniform pair `W₁ k` if
`k < j n`, the challenge `splitHalves z` if `k = j n`, and `G(W₀ k)` otherwise
(`challengeStream`), then `n − i − 1` evaluations of `E` with half selection
(`exists_ggmPRF_evaluator`'s loop); `acc` is "the move is a verdict", `out` the verdict bit.
The functional identity `B.distinguisher n (2n) z r = ggmBitsDist (G n) (D^{(q n)}) … z (c r)`
is proved by induction on the query tree (`buildTree`, `QueryTree.evalLazy`, `levelAdv`,
`tableDist`), and the coin reindexing `c` is a bijection
`Fin (B.coinLen n) → Bool ≃ ((Fin q → Fin n → Bool) × (Fin q → (Fin n → Bool) × (Fin n → Bool))) × D.Coins n`
(`FunFamily.blocks`, `Fin.appendEquiv`, `splitHalves`), so `acceptProb_comp_equiv` gives the
equality of advantages. -/
theorem exists_ggmBitsDist_nuppt {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (hG : ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)) (D : NUPPT)
    (q : PolyExpr) (i j : ℕ → ℕ) :
    ∃ B : NUPPT, ∀ n (hi : i n < n) (hj : j n < q.eval n),
      prgAdv (G n) (B.distinguisher n (2 * n)) =
        prgAdv (G n) (ggmBitsDist (G n) (D.toOracleAdversary n n n (q.eval n)) (q.eval n)
          ⟨i n, hi⟩ ⟨j n, hj⟩) := by
  refine ⟨GGMRed.ggmRedMachine hE D q i j, fun n hi hj => ?_⟩
  have hA : D.toOracleAdversary n n n (q.eval n) = fun r =>
      GGMRed.buildTreeQ (fun hist => D.runAt n (GGMRed.histEnc hist) r) (q.eval n) [] := by
    funext r
    exact buildTree_eq_buildTreeQ _ (q.eval n) []
  rw [hA]
  let e₁ : (Fin (q.eval n) → (Fin n → Bool) × (Fin n → Bool)) ≃ (Fin (q.eval n * (2 * n)) → Bool) :=
    (Equiv.piCongrRight fun _ => splitHalves.symm).trans (FunFamily.blocks (q.eval n) (2 * n)).symm
  let e : ((Fin (q.eval n) → Fin n → Bool) × (Fin (q.eval n) → (Fin n → Bool) × (Fin n → Bool))) ×
      D.Coins n ≃ (GGMRed.ggmRedMachine hE D q i j).Coins n :=
    (Equiv.prodAssoc _ _ _).trans
      (((FunFamily.blocks (q.eval n) n).symm.prodCongr
        ((e₁.prodCongr (Equiv.refl (D.Coins n))).trans
          (Fin.appendEquiv (q.eval n * (2 * n)) (D.coinLen n)))).trans
        (Fin.appendEquiv (q.eval n * n) (q.eval n * (2 * n) + D.coinLen n)))
  refine prgAdv_coins_equiv (G n) _ _ e fun z c => ?_
  obtain ⟨⟨W₁, W₂⟩, r⟩ := c
  refine GGMRed.ggmRedMachine_distinguisher hE D q i j (G n) (hG n) hi hj z (W₁, W₂) r
    (e ((W₁, W₂), r)) ?_
  show List.ofFn (Fin.appendEquiv (q.eval n * n) (q.eval n * (2 * n) + D.coinLen n)
    ((FunFamily.blocks (q.eval n) n).symm W₁,
      Fin.appendEquiv (q.eval n * (2 * n)) (D.coinLen n) (e₁ W₂, r))) = _
  rw [ofFn_appendEquiv, ofFn_appendEquiv]
  rfl

/-- **A next-query machine with query budget `0` has PRF advantage `0`:** with budget `0` the
tree `buildTree … 0 []` is a leaf whose verdict depends on the coins only, so both acceptance
probabilities are the same average over the coins (`uprob_snd`). -/
private theorem prfAdv_toOracleAdversary_zero
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) (D : NUPPT) (n : ℕ) :
    prfAdv (F n) (D.toOracleAdversary n n n 0) = 0 := by
  have hA : ∀ r, ∃ b : Bool, D.toOracleAdversary n n n 0 r = .ret b := by
    intro r
    unfold NUPPT.toOracleAdversary buildTree
    cases decodeOracleMove n (D.runAt n (encodeHist []) r) with
    | ret b => exact ⟨b, rfl⟩
    | query x => exact ⟨false, rfl⟩
  choose b hb using hA
  have key : ∀ {σ : Type} [Fintype σ] [Nonempty σ] (X : σ → (Fin n → Bool) → (Fin n → Bool)),
      acceptProb X (oracleDist (D.toOracleAdversary n n n 0)) =
        uprob fun r : D.Coins n => b r = true := by
    intro σ _ _ X
    unfold acceptProb
    rw [← uprob_snd (α := σ) (fun r : D.Coins n => b r = true)]
    refine uprob_congr fun z => ?_
    rw [oracleDist, hb z.2]
    rfl
  rw [prfAdv, distAdv, key, key, sub_self, abs_zero]

/-- **[PS10, Theorem 97.3] (Goldreich–Goldwasser–Micali): the GGM family of a length-doubling
pseudorandom generator is a pseudorandom function.**

**Proof sketch.** *Easy:* `exists_ggmPRF_evaluator` from `hG.easy`. *Pseudorandom:* fix a
next-query machine `D` and a budget `q`; we show `μ n := prfAdv (G n) (D^{(q n)})` is
negligible (`prfAdv_toOracleAdversary`). Suppose not; by `not_negligible_iff` there is `c` with
`μ n > 1/n^c` for infinitely many `n`. *Concrete step* (Thm-97.3.1, Thm-97.3.2): at every `n` with
`0 < n` and `0 < q n`, `exists_ggmBits_dist (G n) (D^{(q n)}) (toOracleAdversary_boundedBy …)`
gives indices `(i n, j n)` with `μ n / (n · q n) ≤ prgAdv (G n) (ggmBitsDist … (i n) (j n))`
(choose them by `Classical.choose`; put `(0, 0)` elsewhere). *Machine step* (Thm-97.3.3):
`exists_ggmBitsDist_nuppt hE hG D q i j` yields one non-uniform PPT `B` with
`prgAdv (G n) (B.distinguisher n (2n)) = prgAdv (G n) (ggmBitsDist … (i n) (j n))` at those `n`.
*Asymptotic step:* `hG.negligible_prgAdv B` says `ν n := prgAdv (G n) (B.distinguisher n (2n))`
is negligible, hence so is `n · q n · ν n` (`Negligible.mul_pow` with `q n ≤ C (n+1)^d` from
`PolyExpr.eval_le`, `Negligible.const_mul`, `Negligible.mono`), while `μ n ≤ n · q n · ν n`
infinitely often contradicts `μ n > 1/n^c` (`not_negligible_iff`); at the finitely many `n` with
`q n = 0` the adversary makes no query and `μ n = 0` (`buildTree` with budget `0` is a leaf
whose verdict does not depend on the oracle, `distAdv` of a constant distinguisher is `0`). -/
theorem ggmPRF_prf {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)} (hG : DoublingPRG G) :
    PRF (ggmPRF G) := by
  obtain ⟨E, hE, hGE⟩ := hG.easy
  refine ⟨exists_ggmPRF_evaluator hE hGE, fun D q => ?_⟩
  show Negligible fun n => prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n))
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  have hidx : ∀ n, 0 < n → 0 < q.eval n → ∃ (i : Fin n) (j : Fin (q.eval n)),
      prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n)) / (n * q.eval n) ≤
        prgAdv (G n) (ggmBitsDist (G n) (D.toOracleAdversary n n n (q.eval n)) (q.eval n) i j) :=
    fun n hn hq => exists_ggmBits_dist (G n) _ (D.toOracleAdversary_boundedBy n n n (q.eval n)) hn hq
  classical
  let i : ℕ → ℕ := fun n =>
    if h : 0 < n ∧ 0 < q.eval n then (Classical.choose (hidx n h.1 h.2)).val else 0
  let j : ℕ → ℕ := fun n =>
    if h : 0 < n ∧ 0 < q.eval n then
      (Classical.choose (Classical.choose_spec (hidx n h.1 h.2))).val else 0
  obtain ⟨B, hB⟩ := exists_ggmBitsDist_nuppt hE hGE D q i j
  obtain ⟨n₀, hn₀⟩ := (hG.negligible_prgAdv B).polyExpr_mul (.mul .var q) c
  obtain ⟨n, hn, hμn⟩ := hc (max n₀ 1)
  have hn1 : 0 < n := le_of_max_le_right hn
  have hpos : (0 : ℝ) < 1 / (n : ℝ) ^ c := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    positivity
  by_cases hq : 0 < q.eval n
  · have hgood : 0 < n ∧ 0 < q.eval n := ⟨hn1, hq⟩
    have hin : i n = (Classical.choose (hidx n hn1 hq)).val := by simp [i, hgood]
    have hjn : j n = (Classical.choose (Classical.choose_spec (hidx n hn1 hq))).val := by
      simp [j, hgood]
    have hi : i n < n := hin ▸ (Classical.choose (hidx n hn1 hq)).isLt
    have hj : j n < q.eval n :=
      hjn ▸ (Classical.choose (Classical.choose_spec (hidx n hn1 hq))).isLt
    have hspec := Classical.choose_spec (Classical.choose_spec (hidx n hn1 hq))
    have hBn := hB n hi hj
    have hfin : (⟨i n, hi⟩ : Fin n) = Classical.choose (hidx n hn1 hq) := Fin.ext hin
    have hfin' : (⟨j n, hj⟩ : Fin (q.eval n)) =
        Classical.choose (Classical.choose_spec (hidx n hn1 hq)) := Fin.ext hjn
    rw [hfin, hfin'] at hBn
    rw [← hBn] at hspec
    have hbound := hn₀ n (le_of_max_le_left hn)
    simp only [PolyExpr.eval_mul, PolyExpr.eval_var, Nat.cast_mul] at hbound
    have hnq : (0 : ℝ) < (n : ℝ) * (q.eval n : ℝ) := by
      have h1 : (0 : ℝ) < n := by exact_mod_cast hn1
      have h2 : (0 : ℝ) < q.eval n := by exact_mod_cast hq
      positivity
    rw [div_le_iff₀ hnq] at hspec
    have h0 : 0 ≤ prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n)) := prfAdv_nonneg _ _
    rw [abs_of_nonneg h0] at hμn
    have h3 := le_abs_self ((n : ℝ) * (q.eval n : ℝ) * prgAdv (G n) (B.distinguisher n (2 * n)))
    linarith
  · have hq0 : q.eval n = 0 := Nat.eq_zero_of_not_pos hq
    rw [hq0, prfAdv_toOracleAdversary_zero, abs_zero] at hμn
    linarith

/-- **[PS10, Theorem 97.3], as stated: if a pseudorandom generator exists, then pseudorandom
functions exist.** From a secure `PRG` build the length-doubling generator `P.doubling`
(Cor-97.a, `PRG.Secure.doubling`) and take its GGM family (`ggmPRF_prf`). -/
theorem exists_prf_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool), PRF F :=
  let ⟨P, hP⟩ := h
  ⟨ggmPRF P.doubling, ggmPRF_prf hP.doubling⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/PRFLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Pseudorandom.Functions.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for pseudorandom functions: truncation and the GGM evaluator

Machine-level and bit-string infrastructure for `TCSlib.Cryptography.Asymptotic.PRF`
([PS10, §3.8, Theorem 97.3]): the reduction from an arbitrary generator to a length-doubling
one (Cor-97.a, "without loss of generality") and the efficiency clause of the GGM family
(Claim-97.c). Everything here is (i) a bit-string identity between `List.ofFn` encodings and
`List.take`/`List.drop`, (ii) a machine of the closure calculus of
`TCSlib.Complexity.Randomized` (foundation decision D2 of `PassShelatChapter2-4Plan.md`), or
(iii) a probability identity on uniform strings.

* **Truncation.** `Complexity.NUPPT.preComp` is the *parameter-aware* pre-processor: the
  machine `A(1^n, pre ⟨1^n, y⟩; r)` with `A`'s coins and advice (the catalogue's
  `NUPPT.exists_comp` pre-processes the argument without seeing `1^n`, which a truncation to
  `n + 1` bits needs). `acceptProb_castLE` says that the first `m` bits of a uniform `ℓ`-bit
  string are uniform, and `PRG.Secure.truncateTo_easy` / `PRG.Secure.truncateTo_negligible`
  are the two clauses of "the first `m(n) ≤ ℓ(n)` output bits of a secure generator form a
  secure generator", from which `PRG.Secure.truncate` and `PRG.Secure.doubling` follow.
* **The GGM evaluator.** `ggmStep E` is one step of the walk down the GGM tree on the state
  word `⟨y, rest⟩` (current label, remaining input bits): it replaces `y` by the half of
  `E y` selected by the head bit of `rest` and drops that bit; `ggmEval E` iterates it
  `|⟨s, x⟩|` times (`Complexity.polyTimeComputable_iterate`) and reads the label. The closed
  form `ggmStep_iterate` and `ggmFrom_eq_walk` identify the result with `ggmBits G s x`.

## Main definitions

* `Complexity.NUPPT.preComp` — parameter-aware polynomial-time pre-processing of an `NUPPT`.
* `TCSlib.Cryptography.selHalf`, `TCSlib.Cryptography.walk`, `TCSlib.Cryptography.ggmStep`,
  `TCSlib.Cryptography.ggmEval` — half selection, the tree walk and the GGM evaluator.

## Main results

* `TCSlib.Cryptography.take_ofFn_castLE`, `drop_take_ofFn_blocks`, `ofFn_prefixAt`,
  `take_ofFn_splitHalves`, `drop_ofFn_splitHalves`, `selHalf_ofFn` — the bit-string identities.
* `Complexity.NUPPT.runAt_preComp` — the activation of the pre-processed machine.
* `TCSlib.Cryptography.acceptProb_castLE` — a prefix of a uniform string is uniform.
* `TCSlib.Cryptography.PRG.Secure.truncateTo_easy`,
  `TCSlib.Cryptography.PRG.Secure.truncateTo_negligible` — truncation of a secure generator.
* `TCSlib.Cryptography.ggmFrom_eq_walk`, `TCSlib.Cryptography.ggmStep_iterate`,
  `TCSlib.Cryptography.ggmEval_poly`, `TCSlib.Cryptography.ggmEval_ofFn` — the GGM
  evaluator is polynomial-time and computes `ggmBits`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8: Theorem 97.3 and its proof; §3.3.5: Lemma 80.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2 (Construction 3.3, footnote 4).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Bit-string identities -/

/-- The first `m` bits of the encoding of an `ℓ`-bit string (`m ≤ ℓ`) encode its restriction
along `Fin.castLE`. -/
theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i) := by
  refine List.ext_getElem (by simp [List.length_take, h]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  rfl

/-- Block `k` of the encoding of a `q`-tuple of `ℓ`-bit strings (positions `ℓk, …, ℓk + ℓ − 1`)
is the encoding of the `k`-th component, read through `FunFamily.blocks`. -/
theorem drop_take_ofFn_blocks (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) {k : ℕ} (hk : k < q) :
    ((List.ofFn w).drop (ℓ * k)).take ℓ = List.ofFn (FunFamily.blocks q ℓ w ⟨k, hk⟩) := by
  have hlen : ℓ * k + ℓ ≤ q * ℓ := by
    have : (k + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ hk
    nlinarith
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.length_take, List.length_drop, List.length_ofFn] at hj₁
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    show w _ = w (finProdFinEquiv (⟨k, hk⟩, ⟨j, by omega⟩))
    congr 1
    ext
    simp only [finProdFinEquiv, Equiv.coe_fn_mk]
    omega

/-- The encoding of the `i`-bit prefix `prefixAt x i` (`i ≤ n`) is the first `i` bits of the
encoding of `x`. -/
theorem ofFn_prefixAt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i ≤ n) :
    List.ofFn (prefixAt x i) = (List.ofFn x).take i := by
  rw [take_ofFn_castLE hi]
  congr 1
  funext k
  have hk : (k : ℕ) < n := lt_of_lt_of_le k.isLt hi
  simp only [prefixAt, hk, dite_true]
  rfl

/-- The first `n` bits of the encoding of a `2n`-bit string encode the first component of
`splitHalves`. -/
theorem take_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).take n = List.ofFn (splitHalves z).1 := by
  rw [take_ofFn_castLE (by omega)]
  rfl

/-- The last `n` bits of the encoding of a `2n`-bit string encode the second component of
`splitHalves`. -/
theorem drop_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).drop n = List.ofFn (splitHalves z).2 := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_drop, List.getElem_ofFn]
  rfl

/-- **Half selection on strings:** the first (`b = false`) or the last (`b = true`) `|u|` bits
of the word `v` — `g_b(x)` of [PS10, Theorem 97.3] read off the string `g(x) = g₀(x) ‖ g₁(x)`
with the reference length `|u| = n`. -/
def selHalf (b : Bool) (u v : List Bool) : List Bool :=
  if b then (v.drop u.length).take u.length else v.take u.length

/-- Half selection on the encoding of a `2n`-bit string (reference length `n`) is the
encoding of `pairSel b (splitHalves z)`. -/
theorem selHalf_ofFn {n : ℕ} (b : Bool) {u : List Bool} (hu : u.length = n)
    (z : Fin (2 * n) → Bool) :
    selHalf b u (List.ofFn z) = List.ofFn (pairSel b (splitHalves z)) := by
  cases b
  · simp only [selHalf, pairSel, Bool.false_eq_true, if_false, hu, take_ofFn_splitHalves]
  · simp only [selHalf, pairSel, if_true, hu, drop_ofFn_splitHalves]
    exact List.take_of_length_le (le_of_eq List.length_ofFn)

/-- Half selection is at most as long as the reference word. -/
theorem length_selHalf_le (b : Bool) (u v : List Bool) : (selHalf b u v).length ≤ u.length := by
  unfold selHalf
  split_ifs <;> exact List.length_take_le _ _

/-- Half selection is polynomial-time in its three polynomial-time arguments (the typed cuts
`takeLen_poly`/`dropLen_poly` and `Complexity.polyTimeComputable_ite`). -/
theorem selHalf_poly {p : List Bool → Bool} {u v : List Bool → List Bool}
    (hp : PolyTimeComputable fun w => [p w]) (hu : PolyTimeComputable u)
    (hv : PolyTimeComputable v) : PolyTimeComputable fun w => selHalf (p w) (u w) (v w) :=
  polyTimeComputable_ite hp (takeLen_poly hu (dropLen_poly hu hv)) (takeLen_poly hu hv)

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## Parameter-aware pre-processing -/

/-- The raw function of the parameter-aware pre-processor on the layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`:
run `A.output` on `⟨⟨⟨1^n, pre ⟨1^n, y⟩⟩, α⟩, r⟩`. -/
def preFun (A : NUPPT) (pre : List Bool → List Bool) (z : List Bool) : List Bool :=
  A.output (layout (inParam z) (pre (pairEncode (inParam z) (inArg z))) (inAdvice z) (inCoins z))

/-- The raw function of the pre-processor is polynomial-time. -/
theorem preFun_poly (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    PolyTimeComputable (A.preFun pre) :=
  A.polyTimeComputable_output.comp (polyTimeComputable_layout polyTimeComputable_inParam
    (hpre.comp (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
    polyTimeComputable_inAdvice polyTimeComputable_inCoins)

/-- **Parameter-aware pre-processing** [PS10, §2.1, the closure properties used implicitly]:
the machine with `A`'s coins and advice computing `A(1^n, pre ⟨1^n, y⟩; r)`. Unlike
`NUPPT.exists_comp`, the pre-processing sees the parameter (needed to truncate an input to
`n + 1` bits). The coin type is definitionally `A.Coins n`. -/
noncomputable def preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : NUPPT :=
  ofPolyTime (A.preFun_poly hpre) A.coins A.adv A.advice A.advice_length

/-- The coin polynomial of the pre-processed machine is `A`'s. -/
@[simp] theorem coins_preComp (A : NUPPT) {pre : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) : (A.preComp hpre).coins = A.coins := rfl

/-- The untyped activation of the pre-processed machine. -/
theorem runAtL_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y r : List Bool) :
    (A.preComp hpre).runAtL n y r = A.runAtL n (pre (pairEncode (List.replicate n true) y)) r := by
  unfold preComp
  rw [runAtL_ofPolyTime]
  simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- The typed activation of the pre-processed machine (its coin type is `A.Coins n`). -/
theorem runAt_preComp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y : List Bool) (r : (A.preComp hpre).Coins n) :
    (A.preComp hpre).runAt n y r = A.runAt n (pre (pairEncode (List.replicate n true) y)) r :=
  runAtL_preComp A hpre n y (List.ofFn r)

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Truncation of a secure generator -/

/-- **A prefix of a uniform string is uniform:** restricting a uniform `ℓ`-bit string to its
first `m ≤ ℓ` bits gives a uniform `m`-bit string, so a distinguisher accepts the restriction
with the probability with which it accepts a uniform `m`-bit string. (Split the string along
`Fin ℓ ≃ Fin m ⊕ Fin (ℓ − m)` and forget the independent second half, `acceptProb_fst`.) -/
theorem acceptProb_castLE {ℓ m : ℕ} (h : m ≤ ℓ) {ρ : Type*} [Fintype ρ]
    (D : (Fin m → Bool) → ρ → Bool) :
    acceptProb (fun t : Fin ℓ → Bool => fun i : Fin m => t (Fin.castLE h i)) D =
      acceptProb (id : (Fin m → Bool) → Fin m → Bool) D := by
  let e : (Fin ℓ → Bool) ≃ (Fin m → Bool) × (Fin (ℓ - m) → Bool) :=
    ((Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h)).symm (Equiv.refl Bool)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _)))
  have he : (fun t : Fin ℓ → Bool => fun i : Fin m => t (Fin.castLE h i)) =
      fun t => (e t).1 := by
    funext t i
    rfl
  rw [he, acceptProb_comp_equiv e (fun p => p.1) D]
  exact acceptProb_fst (τ := Fin (ℓ - m) → Bool) (id : (Fin m → Bool) → Fin m → Bool) D

/-- **Truncation of a secure generator, efficiency clause:** the first `m(n) ≤ ℓ(n)` output
bits of a secure generator are computed by a polynomial-time string function (the evaluator
followed by the typed cut `Complexity.polyTimeComputable_pairTakePoly m`). -/
theorem PRG.Secure.truncateTo_easy {P : PRG} (hP : P.Secure) (m : PolyExpr)
    (hm : ∀ n, m.eval n ≤ P.stretch.eval n) :
    ∃ E' : List Bool → List Bool, PolyTimeComputable E' ∧
      ∀ n (s : Fin n → Bool),
        E' (List.ofFn s) = List.ofFn fun i : Fin (m.eval n) => P.G n s (Fin.castLE (hm n) i) := by
  obtain ⟨E, hE, hEs⟩ := hP.1
  refine ⟨fun w => (E w).take (m.eval w.length), ?_, fun n s => ?_⟩
  · convert (polyTimeComputable_pairTakePoly m).comp (polyTimeComputable_id.pairEncode hE) using 1
    funext w
    simp
  · simp only [List.length_ofFn]
    rw [hEs, take_ofFn_castLE (hm n)]

/-- **Truncation of a secure generator, pseudorandomness clause:** for every non-uniform PPT
`D`, the PRG advantage of `D(1^n, ·)` against the first `m(n) ≤ ℓ(n)` output bits of a secure
generator is negligible.

**Proof sketch.** The machine `D' := D.preComp (take m)` truncates its `ℓ(n)`-bit input to
`m(n)` bits and runs `D` (`Complexity.NUPPT.preComp`, `runAt_preComp`,
`take_ofFn_castLE`), so `D'.distinguisher n ℓ(n) = D.distinguisher n m(n) ∘ castLE`. By the
sunglass identity `distAdv_comp` its advantage against `G n` is the advantage of `D` between
the truncated generator and the truncation of a uniform `ℓ(n)`-bit string, which is uniform
(`acceptProb_castLE`). Security of `P` makes the former negligible. -/
theorem PRG.Secure.truncateTo_negligible {P : PRG} (hP : P.Secure) (m : PolyExpr)
    (hm : ∀ n, m.eval n ≤ P.stretch.eval n) (D : NUPPT) :
    Negligible fun n =>
      prgAdv (fun s : Fin n → Bool => fun i : Fin (m.eval n) => P.G n s (Fin.castLE (hm n) i))
        (D.distinguisher n (m.eval n)) := by
  have hpre : PolyTimeComputable fun w => (pairSndD w).take (m.eval (pairFstD w).length) :=
    polyTimeComputable_pairTakePoly m
  have hneg := hP.2 (D.preComp hpre)
  refine hneg.mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  have hfun : (D.preComp hpre).distinguisher n (P.stretch.eval n) =
      fun t r => D.distinguisher n (m.eval n) (fun i => t (Fin.castLE (hm n) i)) r := by
    funext t r
    unfold NUPPT.distinguisher
    rw [NUPPT.runAt_preComp]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    rw [take_ofFn_castLE (hm n)]
  show prgAdv (fun s : Fin n → Bool => fun i : Fin (m.eval n) => P.G n s (Fin.castLE (hm n) i))
      (D.distinguisher n (m.eval n)) =
    prgAdv (P.G n) ((D.preComp hpre).distinguisher n (P.stretch.eval n))
  rw [hfun, prgAdv, prgAdv,
    distAdv_comp (fun t : Fin (P.stretch.eval n) → Bool => fun i : Fin (m.eval n) =>
      t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv, distAdv]
  congr 2
  exact (acceptProb_castLE (hm n) _).symm

/-! ## The GGM evaluator -/

/-- **One step of the walk down the GGM tree** on the state word `⟨y, rest⟩` (current label
`y`, remaining input bits `rest`): if `rest` is empty, stay; otherwise replace `y` by the half
of `E y` selected by the head bit of `rest` (`selHalf`, reference length `|y|`) and drop that
bit. `E` is the evaluator of the length-doubling generator. -/
def ggmStep (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  if pairSndD w = [] then w
  else pairEncode (selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)))
    (pairSndD w).tail

/-- The walk down the tree from the label `y` along the bits `bs`:
`walk G' y [b₁, …, b_k] = G'_{b_k}(⋯ G'_{b₁}(y) ⋯)`. -/
def walk {S : Type} (G' : S → S × S) (y : S) (bs : List Bool) : S :=
  bs.foldl (fun y b => pairSel b (G' y)) y

/-- `ggmFrom G' x i y` is the walk from `y` along the bits of `x` from position `i` on
(strong induction on `n − i`, `ggmFrom_of_lt`, `ggmFrom_of_le`). -/
theorem ggmFrom_eq_walk {S : Type} (G' : S → S × S) {n : ℕ} (x : Fin n → Bool) :
    ∀ (i : ℕ) (y : S), ggmFrom G' x i y = walk G' y ((List.ofFn x).drop i)
  | i, y => by
    by_cases h : i < n
    · rw [ggmFrom_of_lt G' x h, ggmFrom_eq_walk G' x (i + 1)]
      have hd : (List.ofFn x).drop i = x ⟨i, h⟩ :: (List.ofFn x).drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_ofFn]
      rw [hd, walk, walk, List.foldl_cons]
    · rw [ggmFrom_of_le G' x (not_lt.1 h), List.drop_of_length_le (by simpa using not_lt.1 h)]
      rfl
termination_by i => n - i

/-- The GGM step never lengthens a word. -/
theorem length_ggmStep_le (E : List Bool → List Bool) (w : List Bool) :
    (ggmStep E w).length ≤ w.length := by
  unfold ggmStep
  split_ifs with h
  · exact le_rfl
  · obtain ⟨a, b, hw⟩ : ∃ a b, w = pairEncode a b := by
      cases hd : pairDecode w with
      | none => exact absurd (by simp [pairSndD, hd]) h
      | some ab => exact ⟨ab.1, ab.2, eq_pairEncode_of_pairDecode w ab.1 ab.2 hd⟩
    subst hw
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h ⊢
    rw [length_pairEncode, length_pairEncode, List.length_tail]
    have h1 := length_selHalf_le (b.headD false) a (E a)
    have h2 : 0 < b.length := List.length_pos_of_ne_nil h
    omega

/-- The orbit of the GGM step stays within the input length. -/
theorem length_ggmStep_iterate_le (E : List Bool → List Bool) (w : List Bool) (k : ℕ) :
    ((ggmStep E)^[k] w).length ≤ w.length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (length_ggmStep_le E _).trans ih

/-- The GGM step is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
of `rest`, `selHalf_poly`, `StateLoop.headBit_poly`, `StateLoop.tail_poly`). -/
theorem ggmStep_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmStep E) := by
  have hsel : PolyTimeComputable fun w =>
      selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)) :=
    selHalf_poly (StateLoop.headBit_poly.comp polyTimeComputable_pairSndD)
      polyTimeComputable_pairFstD (hE.comp polyTimeComputable_pairFstD)
  have htest : PolyTimeComputable fun w => [decide (pairSndD w = [])] :=
    StateLoop.isNil_poly.comp polyTimeComputable_pairSndD
  convert polyTimeComputable_ite htest polyTimeComputable_id
    (hsel.pairEncode (StateLoop.tail_poly.comp polyTimeComputable_pairSndD)) using 1
  funext w
  simp [ggmStep]

/-- **Closed form of the GGM step's orbit on encoded data:** from `⟨s, bs⟩` with `s` an
`n`-bit label, after `k` steps the state is `⟨walk s (bs.take k), bs.drop k⟩`.

**Proof sketch.** Induction on `k`. On an empty `rest` the step is the identity and the walk
is trivial. On `b :: bs` the step replaces the label by the half of `E (ofFn s) = ofFn (G s)`
selected by `b`, which is `ofFn (pairSel b (splitHalves (G s)))` by `selHalf_ofFn`, and drops
`b`; the induction hypothesis from the new label and `bs` finishes. -/
theorem ggmStep_iterate {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s)) :
    ∀ (k : ℕ) (y : Fin n → Bool) (bs : List Bool),
      (ggmStep E)^[k] (pairEncode (List.ofFn y) bs) =
        pairEncode (List.ofFn (walk (splitHalves ∘ G) y (bs.take k))) (bs.drop k)
  | 0, y, bs => by simp [walk]
  | k + 1, y, bs => by
    rw [Function.iterate_succ_apply]
    cases bs with
    | nil =>
      have h0 : ggmStep E (pairEncode (List.ofFn y) []) = pairEncode (List.ofFn y) [] := by
        simp [ggmStep]
      rw [h0, ggmStep_iterate hG k y []]
      simp [walk]
    | cons b bs =>
      have h1 : ggmStep E (pairEncode (List.ofFn y) (b :: bs)) =
          pairEncode (List.ofFn (pairSel b (splitHalves (G y)))) bs := by
        simp only [ggmStep, pairSndD_pairEncode, pairFstD_pairEncode, List.headD_cons,
          List.tail_cons, hG]
        rw [if_neg (List.cons_ne_nil _ _), selHalf_ofFn b List.length_ofFn]
      rw [h1, ggmStep_iterate hG k]
      simp [walk, List.take_succ_cons, List.drop_succ_cons, List.foldl_cons]

/-- **The GGM evaluator** (Claim-97.c): on `⟨s, x⟩` iterate the GGM step `|⟨s, x⟩|` times
(at least `|x|`, after which the step is the identity) and read the label. -/
def ggmEval (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairFstD ((ggmStep E)^[w.length] w)

/-- The GGM evaluator is polynomial-time (`Complexity.polyTimeComputable_iterate` with
`R = P = var`, the orbit staying within the input length). -/
theorem ggmEval_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmEval E) := by
  have h := polyTimeComputable_iterate (ggmStep_poly hE) .var .var
    (fun x i _ => length_ggmStep_iterate_le E x i)
  exact polyTimeComputable_pairFstD.comp h

/-- The GGM evaluator on `⟨s, bs⟩` with an `n`-bit label `s` and an arbitrary bit list `bs`
computes the walk from `s` along `bs` (`ggmStep_iterate`; the word is at least as long as
`bs`, so all bits are consumed). -/
theorem ggmEval_ofFn_walk {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (y : Fin n → Bool) (bs : List Bool) :
    ggmEval E (pairEncode (List.ofFn y) bs) = List.ofFn (walk (splitHalves ∘ G) y bs) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode,
    List.take_of_length_le (by rw [length_pairEncode]; omega)]

/-- **The GGM evaluator computes the GGM family:** on `⟨s, x⟩` with `s, x` `n`-bit strings it
returns the encoding of `ggmBits G s x = g_{x_n}(⋯ g_{x_1}(s) ⋯)` (`ggmStep_iterate`,
`ggmFrom_eq_walk`). -/
theorem ggmEval_ofFn {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (s x : Fin n → Bool) :
    ggmEval E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (ggmBits G s x) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode]
  congr 1
  rw [List.take_of_length_le (by rw [length_pairEncode]; simp)]
  show walk _ s (List.ofFn x) = ggmFrom (splitHalves ∘ G) x 0 s
  rw [ggmFrom_eq_walk, List.drop_zero]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Foundations/Experiments.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.InformationTheory.StatisticalDistance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete security experiments

The concrete layer fixes one value of the security parameter and quantifies over all
adversaries, given as functions of their input and of a uniformly random coin string
from a finite type `ρ`. No running time is imposed here; efficiency is the job of the
asymptotic layer. The experiments are:

* inversion: on `f x` for uniform `x`, output some preimage of `f x`;
* prediction: on `f x`, output the bit `B x`;
* distinguishing: tell apart samples `X s` and `Y t` from uniform seeds `s` and `t`.

Samplers `X : σ → γ` from a finite seed type `σ` describe exactly the distributions
that are pushforwards of uniform coins, which covers every efficiently samplable
ensemble at a fixed parameter.

## Main definitions

* `invProb f A`: the probability that `A` inverts `f`.
* `predProb f B A`: the probability that `A` predicts `B` from `f`.
* `acceptProb X D`: the probability that `D` accepts a sample of `X`.
* `distAdv X Y D`: the distinguishing advantage of `D` between `X` and `Y`.

## Main results

* `acceptProb_comp_equiv`: relabelling the seeds by a bijection preserves acceptance.
* `abs_sum_sub_le_statDist`: a test set distinguishes two distributions by at most
  their statistical distance.
* `distAdv_le_statDist`: the distinguishing advantage of any distinguisher is at most
  the statistical distance of the sampled distributions.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (inversion), Definition 2.3 (prediction),
  Definitions 3.2–3.4 and Lemma 3.1 (distinguishing).
-/

namespace TCSlib.Cryptography

open Finset TCSlib.InformationTheory

variable {α β ρ σ τ γ : Type*} [Fintype α] [Fintype ρ] [Fintype σ] [Fintype τ]

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs a preimage of `f x`. [Gar26, Definition 2.1, Equation (2.1)], at one value of
the security parameter; the input `1^n` is implicit in the fixed types. -/
noncomputable def invProb (f : α → β) (A : β → ρ → α) : ℝ :=
  uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs the bit `B x`. [Gar26, Definition 2.3], at one value of the security
parameter. -/
noncomputable def predProb (f : α → β) (B : α → Bool) (A : β → ρ → Bool) : ℝ :=
  uprob fun z : α × ρ => A (f z.1) z.2 = B z.1

/-- The probability that the distinguisher `D` with uniform coins accepts a sample `X s`
for a uniform seed `s`. [Gar26, Definitions 3.2 and 3.4], the quantities `p(n)` and
`q(n)`. -/
noncomputable def acceptProb (X : σ → γ) (D : γ → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => D (X z.1) z.2 = true

/-- The distinguishing advantage of `D` between the sampled distributions `X` and `Y`,
`|Pr[D(X) = 1] - Pr[D(Y) = 1]|`. [Gar26, Definitions 3.2 and 3.4], the quantity
`Δ_A(n)`. -/
noncomputable def distAdv (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : ℝ :=
  |acceptProb X D - acceptProb Y D|

/-! ### Defining equations

Published so that other layers (the `Games` bridges) read the experiments through stated
equations rather than through their bodies. -/

/-- The defining equation of `invProb`. -/
theorem invProb_def (f : α → β) (A : β → ρ → α) :
    invProb f A = uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1 := rfl

/-- The defining equation of `predProb`. -/
theorem predProb_def (f : α → β) (B : α → Bool) (A : β → ρ → Bool) :
    predProb f B A = uprob fun z : α × ρ => A (f z.1) z.2 = B z.1 := rfl

/-- The defining equation of `acceptProb`. -/
theorem acceptProb_def (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X D = uprob fun z : σ × ρ => D (X z.1) z.2 = true := rfl

/-- The defining equation of `distAdv`. -/
theorem distAdv_def (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D = |acceptProb X D - acceptProb Y D| := rfl

/-- Relabelling the seed space of a sampler by a bijection does not change the probability
that a distinguisher accepts: a bijective image of a uniform seed is uniform. -/
theorem acceptProb_comp_equiv (e : σ ≃ τ) (X : τ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun s => X (e s)) D = acceptProb X D :=
  uprob_comp_equiv (e.prodCongr (Equiv.refl ρ)) (fun z : τ × ρ => D (X z.1) z.2 = true)

/-- The probability that a uniform seed `s` has `X s` in an event `q` is the mass of `q` under
the pushforward of the uniform distribution along `X`. Technical glue between `uprob` and
`FinDist.map`.

**Proof sketch.** Both sides equal `∑ s, [q (X s)] / |σ|`: on the right, group the seeds
by their image under `X`. -/
theorem uprob_comp_eq_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (q : γ → Prop) [DecidablePred q] :
    uprob (fun s => q (X s)) = ∑ g ∈ univ.filter q, (FinDist.uniform σ).map X g := by
  rw [uprob_eq_card_filter, sum_filter]
  have h := Finset.sum_fiberwise' univ X
    (fun g => if q g then (Fintype.card σ : ℝ)⁻¹ else 0)
  have h2 : ∑ s, (if q (X s) then (Fintype.card σ : ℝ)⁻¹ else 0) =
      ((univ.filter fun s => q (X s)).card : ℝ) / Fintype.card σ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [← h2, ← h]
  refine sum_congr rfl fun g _ => ?_
  split_ifs <;> simp [FinDist.map_apply]

/-- The acceptance probability of `D` on samples of `X` is the average over the coins `r` of
the mass, under the distribution of `X`, of the set of samples that `D` accepts with coins
`r`. Technical glue for `distAdv_le_statDist`.

**Proof sketch.** Swap the two coordinates of the sample space, apply Fubini
(`uprob_prod`) to average over the coins first, and rewrite each section with
`uprob_comp_eq_sum_map`. -/
theorem acceptProb_eq_uexp_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (D : γ → ρ → Bool) :
    acceptProb X D = uexp (fun r : ρ => ∑ g ∈ univ.filter (fun g => D g r = true),
        (FinDist.uniform σ).map X g) := by
  rw [acceptProb, ← uprob_comp_equiv (Equiv.prodComm ρ σ), uprob_prod]
  congr 1
  funext r
  exact uprob_comp_eq_sum_map X (fun g => D g r = true)

/-- For any set `T` of outcomes, `|p(T) - q(T)|` is at most the statistical distance of `p`
and `q`. This is the deterministic case of [Gar26, Lemma 3.1].

**Proof sketch.** The differences `d = p - q` sum to zero, so the sum of `d` over the
complement of `T` is `-d(T)`. Splitting `∑ |d|` over `T` and its complement and applying
the triangle inequality to each part gives `∑ |d| ≥ 2 |d(T)|`. -/
theorem abs_sum_sub_le_statDist [Fintype γ] (p q : FinDist γ) (T : Finset γ) :
    |∑ g ∈ T, (p g - q g)| ≤ statDist p q := by
  classical
  have h0 : ∑ g, (p g - q g) = 0 := by
    rw [sum_sub_distrib, p.sum_prob, q.sum_prob, sub_self]
  have hsplit := sum_add_sum_compl T (fun g => p g - q g)
  have habs := sum_add_sum_compl T (fun g => |p g - q g|)
  have h1 := abs_sum_le_sum_abs (fun g => p g - q g) T
  have h2 := abs_sum_le_sum_abs (fun g => p g - q g) Tᶜ
  have hneg : ∑ g ∈ Tᶜ, (p g - q g) = -∑ g ∈ T, (p g - q g) := by linarith
  rw [hneg, abs_neg] at h2
  rw [statDist]
  linarith

/-- The distinguishing advantage of any distinguisher, deterministic or with coins, is at
most the statistical distance of the two sampled distributions. [Gar26, Lemma 3.1].

**Proof sketch.** Average over the coins (`acceptProb_eq_uexp_sum_map`): for fixed coins
`r` the distinguisher is a test set `T_r`, whose advantage is `|X(T_r) - Y(T_r)|`. By
`abs_sum_sub_le_statDist` each of these is at most the statistical distance, and the
absolute value of an average is at most the average of the absolute values. -/
theorem distAdv_le_statDist [Nonempty σ] [Nonempty τ] [Nonempty ρ] [Fintype γ]
    [DecidableEq γ] (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤
      statDist ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  have hρ : (0 : ℝ) < Fintype.card ρ := Nat.cast_pos.2 Fintype.card_pos
  rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
    ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm, ← nsmul_eq_mul, ← card_univ, ← sum_const]
  refine sum_le_sum fun r _ => ?_
  rw [← sum_sub_distrib]
  exact abs_sum_sub_le_statDist _ _ _

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Foundations/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform probability on finite types

Every probability in the concrete layer of the cryptography development is the
probability of an event under the uniform distribution on a finite type: inputs, keys
and coin strings are uniform, and an experiment's sample space is the product of their
types. So probabilities are exact counts, `uprob p = |{a | p a}| / |α|`, and
expectations are averages. Distributions that are not uniform arise as pushforwards
of uniform coins.

## Main definitions

* `uprob p`: the probability that a uniformly random element satisfies `p`.
* `uexp f`: the average of a real function over a finite type.

## Main results

* `uprob_nonneg`, `uprob_le_one`, `uprob_not`, `uprob_mono`, `uprob_or_le`,
  `uprob_exists_le`: basic laws and the union bound.
* `uprob_prod`: probability over a product is the average of the probabilities of
  the sections.
* `uprob_comp_equiv`: probability is invariant under relabelling by a bijection.
* `half_le_uprob_good`: the averaging argument — if an event has probability at least
  `ε`, then at least an `ε / 2` fraction of first coordinates have a section of
  probability at least `ε / 2`.
* `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`: the hybrid argument for a chain of
  probabilities.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Lemma 2.1) and §3.2 (proof of Lemma 3.3).
-/

namespace TCSlib.Cryptography

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The probability that a uniformly random element of the finite type `α` satisfies `p`,
the number of elements satisfying `p` divided by the number of elements. -/
noncomputable def uprob (p : α → Prop) : ℝ :=
  (Nat.card {a // p a} : ℝ) / Fintype.card α

/-- The average of a real function over the finite type `α`, its expectation under the
uniform distribution. -/
noncomputable def uexp (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

/-- The defining equation of `uexp`: the sum of the values divided by the number of points. -/
theorem uexp_def (f : α → ℝ) : uexp f = (∑ a, f a) / Fintype.card α := rfl

/-- With decidable `p`, the probability counts the elements of the filter. -/
theorem uprob_eq_card_filter (p : α → Prop) [DecidablePred p] :
    uprob p = ((univ.filter p).card : ℝ) / Fintype.card α := by
  rw [uprob, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The probability of an event is the average of its indicator. -/
theorem uprob_eq_uexp (p : α → Prop) [DecidablePred p] :
    uprob p = uexp (fun a => if p a then (1 : ℝ) else 0) := by
  rw [uprob_eq_card_filter, uexp, Finset.sum_boole]

/-- Probabilities are nonnegative. -/
theorem uprob_nonneg (p : α → Prop) : 0 ≤ uprob p := by
  unfold uprob; positivity

/-- Probabilities are at most one. -/
theorem uprob_le_one (p : α → Prop) : uprob p ≤ 1 := by
  classical
  rw [uprob_eq_card_filter]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)

/-- The certain event has probability one on a nonempty type. -/
theorem uprob_true [Nonempty α] : uprob (fun _ : α => True) = 1 := by
  classical
  rw [uprob_eq_card_filter, filter_true, card_univ]
  exact div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The impossible event has probability zero. -/
theorem uprob_false : uprob (fun _ : α => False) = 0 := by
  classical
  rw [uprob_eq_card_filter, filter_false, card_empty, Nat.cast_zero, zero_div]

/-- The complement of an event has probability one minus its probability.

**Proof sketch.** The elements satisfying `p` and those satisfying `¬ p` partition `α`, so
their counts add up to `|α|`. -/
theorem uprob_not [Nonempty α] (p : α → Prop) : uprob (fun a => ¬ p a) = 1 - uprob p := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := filter_card_add_filter_neg_card_eq_card (s := univ) p
  rw [card_univ] at h
  rw [uprob_eq_card_filter, uprob_eq_card_filter, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq hc]
  exact_mod_cast (by omega : (univ.filter fun a => ¬ p a).card + (univ.filter p).card =
    Fintype.card α)

/-- An event implied by another has at least its probability. -/
theorem uprob_mono {p q : α → Prop} (h : ∀ a, p a → q a) : uprob p ≤ uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  gcongr with a
  exact h a

/-- Union bound for two events. -/
theorem uprob_or_le (p q : α → Prop) : uprob (fun a => p a ∨ q a) ≤ uprob p + uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter, uprob_eq_card_filter, ← add_div, filter_or]
  gcongr
  exact_mod_cast card_union_le _ _

/-- Union bound for finitely many events.

**Proof sketch.** The set where some `p i` holds is the union over `i ∈ s` of the sets
where `p i` holds, and the size of a union is at most the sum of the sizes. -/
theorem uprob_exists_le {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    uprob (fun a => ∃ i ∈ s, p i a) ≤ ∑ i ∈ s, uprob (p i) := by
  classical
  rw [uprob_eq_card_filter]
  simp_rw [uprob_eq_card_filter, ← sum_div]
  gcongr
  have : (univ.filter fun a => ∃ i ∈ s, p i a) = s.biUnion (fun i => univ.filter (p i)) := by
    ext a; simp
  rw [this]
  exact_mod_cast card_biUnion_le

/-- Probability over a product is the average over the first coordinate of the
probability of the section: Fubini for uniform distributions.

**Proof sketch.** Count the pairs satisfying `p` by first coordinate:
`|{z | p z}| / (|α| |β|) = (∑ a, |{b | p (a, b)}| / |β|) / |α|`. -/
theorem uprob_prod (p : α × β → Prop) :
    uprob p = uexp (fun a => uprob (fun b => p (a, b))) := by
  classical
  simp_rw [uexp, uprob_eq_card_filter, ← sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
    mul_comm (Fintype.card β : ℝ)]
  congr 1
  simp_rw [card_filter]
  push_cast
  exact Fintype.sum_prod_type _

/-- Relabelling the sample space by a bijection preserves probabilities. In particular a
permutation of a uniform input is uniform. -/
theorem uprob_comp_equiv (e : α ≃ β) (p : β → Prop) : uprob (fun a => p (e a)) = uprob p := by
  rw [uprob, uprob, Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)),
    Fintype.card_congr e]

/-- An event depending only on the first coordinate has the same probability on the
product.

**Proof sketch.** By `uprob_prod`, the section at `a` is the certain or the impossible
event according to `p a`, so its probability is the indicator of `p a`, whose average
is `uprob p`. -/
theorem uprob_fst [Nonempty β] (p : α → Prop) : uprob (fun z : α × β => p z.1) = uprob p := by
  classical
  rw [uprob_prod, uprob_eq_uexp]
  congr 1
  funext a
  by_cases h : p a <;> simp [h, uprob_true, uprob_false]

/-- The averaging argument: if an event on `α × β` has probability at least `ε`, then
the first coordinates whose section has probability at least `ε / 2` have probability
at least `ε / 2`. [Gar26, Lemma 2.1].

**Proof sketch.** For `ε < 0` the claim is trivial, and for empty `α` both sides vanish.
Otherwise every section has probability at most `[a is good] + ε / 2`: a good `a` has
section probability at most `1`, a bad one below `ε / 2`. Averaging over `a` with Fubini
(`uprob_prod`) gives `ε ≤ uprob p ≤ Pr[good] + ε / 2`. -/
theorem half_le_uprob_good (p : α × β → Prop) {ε : ℝ} (h : ε ≤ uprob p) :
    ε / 2 ≤ uprob (fun a => ε / 2 ≤ uprob (fun b => p (a, b))) := by
  classical
  rcases lt_or_ge ε 0 with hε | hε
  · linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  rcases isEmpty_or_nonempty α with hα | hα
  · have : uprob p = 0 := by
      rw [uprob, Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  rw [uprob_prod, uexp] at h
  rw [uprob_eq_uexp, uexp]
  have hpt : ∀ a, uprob (fun b => p (a, b)) ≤
      (if ε / 2 ≤ uprob (fun b => p (a, b)) then (1 : ℝ) else 0) + ε / 2 := by
    intro a
    split_ifs with hg
    · linarith [uprob_le_one (fun b => p (a, b))]
    · linarith
  have hsum := sum_le_sum (fun a (_ : a ∈ univ) => hpt a)
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  rw [le_div_iff₀ hc] at h ⊢
  linarith

/-- The hybrid argument, telescoping form: the gap between the ends of a chain is at
most the sum of the gaps between neighbours. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Induction on `t` with the triangle inequality
`|P 0 - P (t+1)| ≤ |P 0 - P t| + |P t - P (t+1)|`. -/
theorem abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) :
    |P 0 - P t| ≤ ∑ i ∈ range t, |P i - P (i + 1)| := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    exact (abs_sub_le _ _ _).trans (add_le_add_right ih _)

/-- The hybrid argument: in a chain of `t ≥ 1` steps some neighbouring pair is at least
a `1 / t` fraction of the end-to-end gap apart. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Otherwise the telescoping bound gives a sum below `t · (gap / t)`. -/
theorem exists_hybrid_gap (P : ℕ → ℝ) {t : ℕ} (ht : 0 < t) :
    ∃ k < t, |P 0 - P t| / t ≤ |P k - P (k + 1)| := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i ∈ range t, |P i - P (i + 1)| < ∑ _i ∈ range t, |P 0 - P t| / t :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.2 ht.ne') fun i hi => hcon i (mem_range.1 hi)
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ htR] at hlt
  linarith [abs_sub_le_sum_hybrids P t]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Games/Advantage.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advantages of game-playing adversaries

Security definitions come in three shapes, each measured at one value of the security parameter:
- a **search game** (forge a tag, find a collision, invert a function): its advantage is the
  probability that the game, run with the adversary, outputs `true`;
- a **distinguishing pair** (real versus random, left versus right): its advantage is the
  difference of the two games' acceptance probabilities;
- a **guess-the-bit game**: a bit `b` is drawn, the game runs on `b`, and the adversary wins if it
  outputs `b`. Its advantage is the distance of the winning probability from `½`, which is half
  the distinguishing advantage of the two games (`guessAdv_eq_half_advantage`).

Games are `ProbComp Bool`s built from the adversary; these shapes are what asymptotic security
definitions wrap with "negligible for every efficient adversary".

## Main definitions

* `Games.accept G`: the probability that `G` outputs `true`.
* `Games.advantage G₀ G₁`: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
* `Games.guessGame G`, `Games.guessAdv G`: the guess-the-bit game over `G : Bool → ProbComp Bool`
  and its advantage `|Pr[win] − ½|`.

## Main results

* `advantage_triangle`, `advantage_hybrid`, `exists_advantage_hybrid_gap`: the hybrid argument;
  the advantage between the ends of a chain of games is at most the sum of the advantages between
  neighbours, so some neighbouring pair carries a `1/n` share of it, for `n` hops
  ([PS10, Lemma 71.6]).
* `guessAdv_eq_half_advantage`: the guess-the-bit advantage is half the distinguishing advantage
  between the games for `b = 1` and `b = 0` (the identity behind [PS10, Lemma 73.8]).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.1 (Def 69.4, computational indistinguishability), Lemma 71.6 (the hybrid lemma), Lemma 73.8
  (the prediction lemma) and Definition 168.1 (the experiments `IND_b` for a fixed challenge bit).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset ProbComp

/-- The probability that the game `G` outputs `true`. -/
noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)

/-- The acceptance probability is the probability of the output `true`:
`accept G = prob G (· = true)`. -/
theorem accept_eq (G : ProbComp Bool) : accept G = prob G (· = true) :=
  rfl

/-- The **distinguishing advantage** between two games: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
[PS10, §3.1] -/
noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|

/-- The distinguishing advantage is the absolute gap of the acceptance probabilities:
`advantage G₀ G₁ = |accept G₀ - accept G₁|`. -/
theorem advantage_eq (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = |accept G₀ - accept G₁| :=
  rfl

/-- An acceptance probability is nonnegative. -/
theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _

/-- An acceptance probability is at most one. -/
theorem accept_le_one (G : ProbComp Bool) : accept G ≤ 1 := prob_le_one G _

/-- The distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (G₀ G₁ : ProbComp Bool) : 0 ≤ advantage G₀ G₁ := abs_nonneg _

/-- The distinguishing advantage is symmetric. -/
theorem advantage_comm (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = advantage G₁ G₀ :=
  abs_sub_comm _ _

/-- A game has no advantage against itself. -/
@[simp] theorem advantage_self (G : ProbComp Bool) : advantage G G = 0 := by simp [advantage]

/-- The distinguishing advantage is at most one. -/
theorem advantage_le_one (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ ≤ 1 := by
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [accept_nonneg G₀, accept_nonneg G₁, accept_le_one G₀, accept_le_one G₁]

/-- **One game hop:** the advantage between `G₀` and `G₂` is at most the sum of the advantages
through `G₁`. -/
theorem advantage_triangle (G₀ G₁ G₂ : ProbComp Bool) :
    advantage G₀ G₂ ≤ advantage G₀ G₁ + advantage G₁ G₂ :=
  abs_sub_le _ _ _

/-- **The hybrid argument:** along a chain of games `G 0, …, G n`, the advantage between the ends
is at most the sum of the advantages between neighbours: the telescoping inequality in the proof of
[PS10, Lemma 71.6]. It is the concrete layer's `abs_sub_le_sum_hybrids` for the acceptance
probabilities. -/
theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) :=
  abs_sub_le_sum_hybrids (fun i => accept (G i)) n

/-- **The hybrid lemma:** along a chain `G 0, …, G n` of `n > 0` hops (`n + 1` games), some
neighbouring pair has advantage at least `advantage (G 0) (G n) / n`. [PS10, Lemma 71.6]

**Deviation:** sharper than the source, which takes `m` distributions (`m − 1` hops), a threshold
`ε < |g₁ − g_m|`, and concludes `> ε/m`. Here the divisor is the number of hops and the bound is
the exact endpoint advantage; the source's form follows with `m = n + 1`. It is the concrete
layer's `exists_hybrid_gap` for the acceptance probabilities. -/
theorem exists_advantage_hybrid_gap (G : ℕ → ProbComp Bool) {n : ℕ} (hn : 0 < n) :
    ∃ i < n, advantage (G 0) (G n) / n ≤ advantage (G i) (G (i + 1)) :=
  exists_hybrid_gap (fun i => accept (G i)) hn

/-! ### Guess-the-bit games -/

/-- The **guess-the-bit game** over `G`: draw a uniform bit `b`, run `G b`, and win if its output
is `b`: the prediction experiment `b ← {0,1}; t ← X^b : A(t) = b` of [PS10, Lemma 73.8], with
`G b` the whole game for challenge bit `b`. -/
noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
  (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))

/-- The guess-the-bit game samples `b`, runs `G b` and outputs whether it returned `b`:
`guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))`. -/
theorem guessGame_eq (G : Bool → ProbComp Bool) :
    guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b)) :=
  rfl

/-- The **guess-the-bit advantage**: how far the winning probability is from `½`. -/
noncomputable def guessAdv (G : Bool → ProbComp Bool) : ℝ := |accept (guessGame G) - 1 / 2|

/-- The winning probability of the guess-the-bit game is the average of `Pr[G 1 = 1]` and
`Pr[G 0 = 0]`. [PS10, proof of Lemma 73.8]

**Proof sketch.** Total probability over the uniform bit (two equally likely values), and
`Pr[G 0 = 0] = 1 − Pr[G 0 = 1]`. -/
theorem accept_guessGame (G : Bool → ProbComp Bool) :
    accept (guessGame G) = (accept (G true) + (1 - accept (G false))) / 2 := by
  classical
  have hnot : prob (G false) (· = false) = 1 - accept (G false) := by
    rw [accept, ← prob_not]
    exact prob_congr _ fun b => by cases b <;> simp
  unfold accept guessGame
  rw [prob_bind, expect_sample]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton, Fintype.card_bool, prob_bind]
  have h1 : expect (G true) (fun b' => prob (OracleComp.pure (decide (b' = true))) (· = true)) =
      prob (G true) (· = true) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  have h0 : expect (G false) (fun b' => prob (OracleComp.pure (decide (b' = false))) (· = true)) =
      prob (G false) (· = false) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  rw [h1, h0, hnot]
  simp only [accept]
  push_cast
  ring

/-- **Guessing versus distinguishing:** `|Pr[win] − ½| = |Pr[G 1 = 1] − Pr[G 0 = 1]| / 2`. This
is the identity behind [PS10, §3.1.1, Lemma 73.8]: a predictor with success `½ + δ` is a
distinguisher with advantage `2δ`, and conversely.

**Deviation:** stated exactly, at one value of the security parameter, for whole games; the
absolute value replaces the source's "without loss of generality" complement of the distinguisher.
[PS10, Def 168.1] is stated in the distinguishing form only, with its experiments `IND_0`, `IND_1`
as the games `G false`, `G true`. The concrete layer's counterpart is `predict_eq`
(`TCSlib.Cryptography.Asymptotic.Ensembles`). -/
theorem guessAdv_eq_half_advantage (G : Bool → ProbComp Bool) :
    guessAdv G = advantage (G true) (G false) / 2 := by
  unfold guessAdv advantage
  rw [accept_guessGame]
  rw [show (accept (G true) + (1 - accept (G false))) / 2 - 1 / 2 =
      (accept (G true) - accept (G false)) / 2 by ring, abs_div, abs_two]

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/BitCodec.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-string oracles and their machine codec

The security games of [PS10] ch. 5–8 give machine adversaries a finite family of oracles on
fixed-length bit strings: a tagging oracle, a signing oracle, encryption and decryption oracles,
and so on. At parameter `n` oracle `i` takes `din i` bits and answers with `dout i` bits
(`bitSpec`). This file fixes the codec through which a next-move machine (`NUPPT.toComp`) plays
against such a family, and through which it returns a fixed-length output (`bitCodec`):
- **a query** to oracle `i` on `x` is the output `⟨[false], ⟨1^i, x⟩⟩`;
- **a final output** `a` is `⟨[true], a⟩`;
- **anything else**, a malformed or wrong-length string, decodes to the all-`false` output (the
  ch. 2–4 layer's convention D7: ill-formed outputs count as a fixed default);
- **a log entry** `(i, x, y)` is encoded as `⟨1^i, ⟨x, y⟩⟩`;
- **when the query budget runs out**, the output is the all-`false` string.

It is the shared codec of every prong's statements, and the T0 definitions of the efficiency fill
(`briefs/pass-shelat-ch5-8/fills/efficiency/`).

## Main definitions

* `Games.bitSpec din dout`: `k` oracles on fixed-length bit strings.
* `Games.decodeIdx`, `Games.decodeBitMove`: decoding of an oracle index and of a machine output as
  a move.
* `Games.encodeBitMove`: the canonical word of a move.
* `Games.bitCodec din dout dα`: the codec.

## Main results

* `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
  well-formed encodings decode as intended.
* `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
  decode as an index or a query.
* `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines) and Definitions 134.2, 136.2 and 168.1 (oracle adversaries).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- **`k` oracles on fixed-length bit strings:** oracle `i` takes `din i` bits and answers with
`dout i` bits. -/
abbrev bitSpec (din dout : Fin k → ℕ) : OracleSpec (Fin k) :=
  ⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩

/-- Oracle `i` of `bitSpec din dout` takes `din i`-bit strings. -/
theorem bitSpec_dom (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).dom i = (Fin (din i) → Bool) :=
  rfl

/-- Oracle `i` of `bitSpec din dout` answers with `dout i`-bit strings. -/
theorem bitSpec_rng (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).rng i = (Fin (dout i) → Bool) :=
  rfl

/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length at least `k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

/-- The unary code of an index decodes to it. -/
theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
  unfold decodeIdx
  have h : (List.replicate (i : ℕ) true).length < k ∧
      List.replicate (i : ℕ) true =
        List.replicate (List.replicate (i : ℕ) true).length true := by
    simp
  rw [dif_pos h]
  exact congrArg some (Fin.ext (by simp))

/-- **Exactly the unary codes decode**, each to its index:
`decodeIdx k iw = some i ↔ iw = 1^i`. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeIdx_replicate i⟩
  unfold decodeIdx at h
  split_ifs at h with hw
  rw [Option.some.injEq] at h
  rw [← h]
  exact hw.2

/-- **Every other word is rejected:** `decodeIdx k iw = none` exactly when `iw` is the unary code
of no index below `k`. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true := by
  constructor
  · intro h i hi
    rw [decodeIdx_eq_some_iff.2 hi] at h
    exact Option.some_ne_none i h
  · intro h
    cases hd : decodeIdx k iw with
    | none => rfl
    | some i => exact absurd (decodeIdx_eq_some_iff.1 hd) (h i)

/-- The default output: the all-`false` string. -/
def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false

/-- Every bit of the default output is `false`: `zeroBits d j = false`. -/
theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
  rfl

/-- The default output, written as a string, is `d` copies of `false`:
`List.ofFn (zeroBits d) = List.replicate d false`. -/
theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
  rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]

/-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
`⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
`⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
def decodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    Move (bitSpec din dout) (Fin dα → Bool) :=
  match pairDecode w with
  | some ([false], rest) =>
    match pairDecode rest with
    | some (iw, xw) =>
      match decodeIdx k iw with
      | some i =>
        match decodeFin (din i) xw with
        | some x => .query i x
        | none => .ret (zeroBits dα)
      | none => .ret (zeroBits dα)
    | none => .ret (zeroBits dα)
  | some ([true], aw) =>
    match decodeFin dα aw with
    | some a => .ret a
    | none => .ret (zeroBits dα)
  | _ => .ret (zeroBits dα)

/-- **The canonical word of a move:** the query `x` to oracle `i` is `⟨[false], ⟨1^i, x⟩⟩`, and
the output `a` is `⟨[true], a⟩`. `decodeBitMove` inverts it (`decodeBitMove_encodeBitMove`). -/
def encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) :
    Move (bitSpec din dout) (Fin dα → Bool) → List Bool
  | .query i x => pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  | .ret a => pairEncode [true] (List.ofFn a)

/-- The canonical word of a query:
`encodeBitMove din dout dα (query i x) = ⟨[false], ⟨1^i, x⟩⟩`. -/
theorem encodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    encodeBitMove din dout dα (.query i x) =
      pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
  rfl

/-- The canonical word of an output: `encodeBitMove din dout dα (ret a) = ⟨[true], a⟩`. -/
theorem encodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    encodeBitMove din dout dα (.ret a) = pairEncode [true] (List.ofFn a) :=
  rfl

/-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
`(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
    MachineCodec (bitSpec din dout) (Fin dα → Bool) where
  decodeMove := decodeBitMove din dout dα
  encodeEntry e :=
    pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
  timeout := zeroBits dα

/-- The codec decodes moves with `decodeBitMove`: `(bitCodec din dout dα).decodeMove w =
decodeBitMove din dout dα w`. -/
theorem bitCodec_decodeMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    (bitCodec din dout dα).decodeMove w = decodeBitMove din dout dα w :=
  rfl

/-- The codec encodes the log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem bitCodec_encodeEntry (din dout : Fin k → ℕ) (dα : ℕ)
    (e : Σ i, (bitSpec din dout).dom i × (bitSpec din dout).rng i) :
    (bitCodec din dout dα).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  rfl

/-- When the budget runs out, the codec's output is all-`false`:
`(bitCodec din dout dα).timeout = zeroBits dα`. -/
theorem bitCodec_timeout (din dout : Fin k → ℕ) (dα : ℕ) :
    (bitCodec din dout dα).timeout = zeroBits dα :=
  rfl

/-- The codec's log encoding does not depend on the output length: `bitCodec din dout dα` and
`bitCodec din dout dα'` encode every log alike. -/
theorem encodeLog_bitCodec (din dout : Fin k → ℕ) (dα dα' : ℕ) (h : QueryLog (bitSpec din dout)) :
    (bitCodec din dout dα).encodeLog h = (bitCodec din dout dα').encodeLog h := by
  induction h with
  | nil => rw [MachineCodec.encodeLog_nil, MachineCodec.encodeLog_nil]
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih, bitCodec_encodeEntry,
      bitCodec_encodeEntry]

/-- A well-formed query decodes as the query. -/
theorem decodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    decodeBitMove din dout dα
        (pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))) = .query i x := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeIdx_replicate, decodeFin_ofFn]

/-- A well-formed output decodes as the output. -/
theorem decodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    decodeBitMove din dout dα (pairEncode [true] (List.ofFn a)) = .ret a := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- A decoded `ℓ`-bit string is the string itself (read through `decodeFin`'s published lemmas
only). -/
private theorem eq_ofFn_of_decodeFin {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w = List.ofFn x := by
  have hw := length_eq_of_decodeFin_eq_some h
  subst hw
  have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
  rw [List.ofFn_get, h, Option.some.injEq] at h'
  rw [h']
  exact (List.ofFn_get w).symm

/-- **Only the canonical query word decodes as a query:** `decodeBitMove din dout dα w` is the
query `x` to oracle `i` exactly when `w = ⟨[false], ⟨1^i, x⟩⟩` (the converse of
`decodeBitMove_query`).

**Proof sketch.** Follow `decodeBitMove`'s branches: only the branch in which the tag is `[false]`,
the rest parses as a pair, the index word decodes and the payload has the right length returns a
query. There, each successful parse determines its input: a parsed pair is the pairing of its parts
(`eq_pairEncode_of_pairDecode`), a decoded index word is `1^i` (`decodeIdx_eq_some_iff`), and a
decoded payload is `List.ofFn x`. -/
theorem decodeBitMove_eq_query_iff {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool} {i : Fin k}
    {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeBitMove_query din dout dα i x⟩
  unfold decodeBitMove at h
  split at h
  · rename_i rest hw
    split at h
    · rename_i iw xw hr
      split at h
      · rename_i j hj
        split at h
        · rename_i x' hx
          cases h
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr,
            decodeIdx_eq_some_iff.1 hj, eq_ofFn_of_decodeFin hx]
        · cases h
      · cases h
    · cases h
  · split at h <;> cases h
  · cases h

/-- **The default:** a word that is neither a canonical query `⟨[false], ⟨1^i, x⟩⟩` nor a
canonical output `⟨[true], a⟩` decodes to the output `zeroBits dα`. With `decodeBitMove_query`
and `decodeBitMove_ret` this determines `decodeBitMove` on every word.

**Proof sketch.** Follow `decodeBitMove`'s branches. Every branch but two returns `zeroBits dα`.
In the query branch, the successful parses make `w` a canonical query word, as in
`decodeBitMove_eq_query_iff`, against `hq`; in the output branch, they make `w` a canonical output
word, against `hr`. -/
theorem decodeBitMove_of_not_canonical {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα) := by
  unfold decodeBitMove
  split
  · rename_i rest hw
    split
    · rename_i iw xw hr'
      split
      · rename_i j hj
        split
        · rename_i x hx
          refine absurd ?_ (hq j x)
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr',
            decodeIdx_eq_some_iff.1 hj, eq_ofFn_of_decodeFin hx]
        · rfl
      · rfl
    · rfl
  · rename_i aw hw
    split
    · rename_i a ha
      refine absurd ?_ (hr a)
      rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_ofFn_of_decodeFin ha]
    · rfl
  · rfl

/-- **Canonical words decode to their move:** `decodeBitMove (encodeBitMove m) = m`. -/
theorem decodeBitMove_encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ)
    (m : Move (bitSpec din dout) (Fin dα → Bool)) :
    decodeBitMove din dout dα (encodeBitMove din dout dα m) = m := by
  cases m with
  | query i x => exact decodeBitMove_query din dout dα i x
  | ret a => exact decodeBitMove_ret din dout dα a

/-- Distinct moves have distinct canonical words. -/
theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
    Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
  rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Bridges.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Bridges.Strategies

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `Games` framework, connected to machines and to the ch. 2–4 layer

The core framework (`TCSlib.Cryptography.Games`) needs only Mathlib and finite distributions. This
facade adds the layer (S2b of the Pass–shelat ch. 5–8 campaign) that connects it to the machine
model and to the ch. 2–4 layer.

## Contents

* `Games.Machines`: machines as oracle computations (`NUPPT.toComp`, `NUPPT.toCompOn`).
* `Games.BitCodec`: bit-string oracles and their machine codec (`bitSpec`, `bitCodec`).
* `Games.Efficiency`: polynomial-time handlers (adversary input, queries, finalization) and the
  efficiency targets T1 and T2, with their companions (adversaries without input; T4, the bridge
  to the ch. 2–4 next-query machines) (the efficiency fill).
* `Games.Bridges.QueryTree`: the concrete layer's query trees, which *are* one-oracle computations
  (item F-1); their evaluation, simulation and query bounds are the framework's.
* `Games.Bridges.Experiments`: the concrete layer's experiments (`invProb`, `predProb`,
  `acceptProb`, `distAdv`) as games (bridge B2).
* `Games.Bridges.Machines`: the ch. 2–4 next-query machines as an instance of the decoder (B3).
* `Games.Bridges.Strategies`: next-message strategies embedded as parties; the embedded
  execution is D8's (B4).
-/

## ===== TCSlib/Cryptography/Games/Bridges/Experiments.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bridge: the concrete layer's experiments are games

The concrete security layer of the ch. 2–4 development measures its experiments with `uprob`,
the probability that a uniformly random element of a finite type satisfies an event. Its four
experiments are inversion (`invProb`), prediction (`predProb`), acceptance (`acceptProb`) and
distinguishing (`distAdv`). This file shows that each is the probability of a one-line game of the
`Games` framework: sample the seed and the adversary's coins, run the adversary, test. So every
concrete-layer result stated through these quantities transfers to the framework unchanged.

The basic fact is `prob_sample_eq_uprob`: sampling a finite type and testing an event has
probability `uprob` of the event. It reads `uprob` only through its published equation
`uprob_eq_card_filter`. Sampling a pair one component at a time is sampling the product
(`prob_sample_pair`), so the games may sample the seed and the coins in sequence.

The four experiments are read through their published defining equations (`invProb_def`,
`predProb_def`, `acceptProb_def`, `distAdv_def` in `Foundations/Experiments.lean`).

## Main definitions

* `Games.Bridge.acceptGame X D`: the acceptance game of a sampler and a distinguisher.

## Main results

* `Games.Bridge.prob_sample_eq_uprob`: `Pr[x ← $ α : p x] = uprob p`.
* `Games.Bridge.prob_sample_pair`: sampling `α` then `β` is sampling `α × β`.
* `Games.Bridge.invProb_eq`, `predProb_eq`, `acceptProb_eq`, `distAdv_eq`: the four concrete
  experiments as games.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the experiments).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games.Bridge

open Finset ProbComp

variable {α β ρ σ τ γ : Type}

/-- **Sampling and `uprob` agree:** the probability that a uniform sample of the nonempty finite
type `α` satisfies `p` is `uprob p`.

**Proof sketch.** Both are the number of elements satisfying `p` divided by `|α|`: the sample's
probability is the uniform average of the indicator (`expect_sample`), and `uprob` is the
filter's cardinality over `|α|` (`uprob_eq_card_filter`). -/
theorem prob_sample_eq_uprob [Fintype α] [Nonempty α] (p : α → Prop) :
    prob (sample α) p = uprob p := by
  classical
  rw [prob_eq_expect, expect_sample, uprob_eq_card_filter, sum_boole, inv_mul_eq_div]

/-- **Sampling a pair in sequence is sampling the product:** for every function `g` on pairs,
its expectation over `a ← $ α; b ← $ β; (a, b)` equals its expectation over a uniform pair. -/
theorem expect_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (g : α × β → ℝ) :
    expect ((sample α).bind fun a => (sample β).bind fun b => .pure (a, b)) g =
      expect (sample (α × β)) g := by
  rw [expect_bind, expect_sample, expect_sample, Fintype.card_prod, Fintype.sum_prod_type]
  simp only [expect_bind, expect_sample, expect_pure, Nat.cast_mul, mul_inv, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

/-- Sampling a pair in sequence is sampling the product, for probabilities. -/
theorem prob_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (p : α × β → Prop) :
    prob ((sample α).bind fun a => (sample β).bind fun b => .pure (a, b)) p =
      prob (sample (α × β)) p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, expect_sample_pair]

/-- **Inversion as a game:** `invProb f A` is the probability that the game "sample `x` and the
adversary's coins `r`; win if `A (f x) r` is a preimage of `f x`" is won. [Gar26, Def 2.1] -/
theorem invProb_eq [Fintype α] [Nonempty α] [Fintype ρ] [Nonempty ρ] (f : α → β)
    (A : β → ρ → α) :
    invProb f A =
      prob ((sample α).bind fun x => (sample ρ).bind fun r => .pure (x, r))
        (fun z => f (A (f z.1) z.2) = f z.1) := by
  rw [invProb_def, prob_sample_pair, prob_sample_eq_uprob]

/-- **Prediction as a game:** `predProb f B A` is the probability that `A`, given `f x` and its
coins, outputs `B x`. [Gar26, Def 2.3] -/
theorem predProb_eq [Fintype α] [Nonempty α] [Fintype ρ] [Nonempty ρ] (f : α → β)
    (B : α → Bool) (A : β → ρ → Bool) :
    predProb f B A =
      prob ((sample α).bind fun x => (sample ρ).bind fun r => .pure (x, r))
        (fun z => A (f z.1) z.2 = B z.1) := by
  rw [predProb_def, prob_sample_pair, prob_sample_eq_uprob]

/-- The acceptance game of a sampler `X` and a distinguisher `D`: sample the seed and the coins,
and output `D`'s verdict on the sample. -/
noncomputable def acceptGame [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) : ProbComp Bool :=
  (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)

/-- The acceptance game samples the seed `s`, then the coins `r`, and outputs `D (X s) r`:
`acceptGame X D = (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)`. -/
theorem acceptGame_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) :
    acceptGame X D = (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r) :=
  rfl

/-- **Acceptance as a game:** `acceptProb X D` is the acceptance probability of `acceptGame X D`.
[Gar26, Defs 3.2 and 3.4] -/
theorem acceptProb_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) : acceptProb X D = accept (acceptGame X D) := by
  have h : acceptGame X D =
      (fun z : σ × ρ => D (X z.1) z.2) <$>
        ((sample σ).bind fun s => (sample ρ).bind fun r => .pure (s, r)) := by
    simp only [acceptGame_eq, OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [acceptProb_def, accept_eq, h, prob_eq_expect, expect_map, ← prob_eq_expect
    (p := fun z : σ × ρ => D (X z.1) z.2 = true), prob_sample_pair, prob_sample_eq_uprob]

/-- **Distinguishing as a game:** `distAdv X Y D` is the advantage between the acceptance games
of `X` and of `Y`. [Gar26, Defs 3.2 and 3.4] -/
theorem distAdv_eq [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ] [Fintype ρ] [Nonempty ρ]
    (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D = advantage (acceptGame X D) (acceptGame Y D) := by
  rw [distAdv_def, advantage_eq, acceptProb_eq, acceptProb_eq]

end TCSlib.Cryptography.Games.Bridge

## ===== TCSlib/Cryptography/Games/Bridges/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Asymptotic.PRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The ch. 2–4 next-query machines as an instance of the machine decoder

The ch. 2–4 layer's `NUPPT.toOracleAdversary` turns a next-query machine (one oracle on bit
strings, a Boolean verdict) into a query tree. That tree is the generic decoder
`NUPPT.toComp` (`TCSlib.Cryptography.Games.Machines`) with the codec `singleCodec`, built from the
layer's own move decoding `decodeOracleMove` and history encoding `encodeHist`. So
`OracleEnsemble.Indist` (via `oracleDist`) is a statement about framework computations.

## Main definitions

* `Games.singleCodec ℓ₁ ℓ₂`: the codec of the ch. 2–4 next-query machines.

## Main results

* `Games.toComp_singleCodec`: `toOracleAdversary` is the one-oracle instance of `toComp`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 and Definition 96.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

/-! ### The ch. 2–4 next-query machines are an instance -/

/-- The codec of the ch. 2–4 next-query machines: one oracle on bit strings, a Boolean verdict,
moves decoded by `decodeOracleMove`, entries encoded as in `encodeHist`, and the verdict `false`
when the budget runs out. -/
def singleCodec (ℓ₁ ℓ₂ : ℕ) :
    MachineCodec (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)) Bool where
  decodeMove w := match decodeOracleMove ℓ₁ w with
    | .query x => .query () x
    | .ret b => .ret b
  encodeEntry e := pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)
  timeout := false

/-- The codec decodes a move with `decodeOracleMove`, the query `x` becoming a query to the sole
oracle `()`: `(singleCodec ℓ₁ ℓ₂).decodeMove w` is `query () x` when `decodeOracleMove ℓ₁ w` is
`query x`, and `ret b` when it is `ret b`. -/
theorem singleCodec_decodeMove (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
    (singleCodec ℓ₁ ℓ₂).decodeMove w = match decodeOracleMove ℓ₁ w with
      | .query x => .query () x
      | .ret b => .ret b :=
  rfl

/-- The codec encodes the log entry `(x, y)` as `⟨x, y⟩`, as `encodeHist` does. -/
theorem singleCodec_encodeEntry (ℓ₁ ℓ₂ : ℕ)
    (e : Σ u, (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).dom u ×
      (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).rng u) :
    (singleCodec ℓ₁ ℓ₂).encodeEntry e = pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2) :=
  rfl

/-- When the budget runs out, the codec's verdict is `false`. -/
theorem singleCodec_timeout (ℓ₁ ℓ₂ : ℕ) : (singleCodec ℓ₁ ℓ₂).timeout = false :=
  rfl

/-- The ch. 2–4 history of a one-oracle log: the list of its (query, answer) pairs. -/
def toHist {ℓ₁ ℓ₂ : ℕ} (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  h.map fun e => (e.2.1, e.2.2)

/-- The empty log has the empty history: `toHist [] = []`. -/
theorem toHist_nil {ℓ₁ ℓ₂ : ℕ} :
    toHist ([] : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) = [] :=
  rfl

/-- The history of `e :: h` starts with `e`'s (query, answer) pair:
`toHist (e :: h) = (e.2.1, e.2.2) :: toHist h`. -/
theorem toHist_cons {ℓ₁ ℓ₂ : ℕ}
    (e : Σ u, (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).dom u ×
      (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).rng u)
    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    toHist (e :: h) = (e.2.1, e.2.2) :: toHist h :=
  rfl

/-- The history of `h ++ [e]` ends with `e`'s (query, answer) pair:
`toHist (h ++ [e]) = toHist h ++ [(e.2.1, e.2.2)]`. -/
theorem toHist_append_singleton {ℓ₁ ℓ₂ : ℕ}
    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)))
    (e : Σ u, (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).dom u ×
      (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)).rng u) :
    toHist (h ++ [e]) = toHist h ++ [(e.2.1, e.2.2)] := by
  rw [toHist, toHist, List.map_append, List.map_singleton]

/-- The codec's log encoding is the ch. 2–4 history encoding. -/
theorem encodeLog_singleCodec {ℓ₁ ℓ₂ : ℕ}
    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    (singleCodec ℓ₁ ℓ₂).encodeLog h = encodeHist (toHist h) := by
  induction h with
  | nil => rw [MachineCodec.encodeLog_nil, toHist_nil, encodeHist_nil]
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, toHist_cons, encodeHist_cons, ih, singleCodec_encodeEntry]

/-- One step of the correspondence: the framework's computation from a log is the ch. 2–4 tree
from the corresponding history.

**Proof sketch.** Induction on the budget. Both builders branch on the same move `next (toHist
hist)`, by their case equations (`buildComp_zero_of_ret`, …, `buildTree_succ_of_query`): a verdict
or a spent budget gives the same leaf, and a query gives a query node on both sides whose
continuations agree by induction, since `toHist` of the extended log is the extended history. -/
theorem buildComp_singleCodec {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))),
      buildComp (fun h => match next (toHist h) with
          | .query x => .query () x
          | .ret b => .ret b) false q hist =
        buildTree next q (toHist hist)
  | 0, hist => by
    cases hn : next (toHist hist) with
    | ret b => rw [buildComp_zero_of_ret (a := b) (by simp only [hn]), buildTree_zero_of_ret hn]
    | query x =>
      rw [buildComp_zero_of_query (i := ()) (x := x) (by simp only [hn]),
        buildTree_zero_of_query hn]
  | q + 1, hist => by
    cases hn : next (toHist hist) with
    | ret b => rw [buildComp_succ_of_ret (a := b) (by simp only [hn]), buildTree_succ_of_ret hn]
    | query x =>
      rw [buildComp_succ_of_query (i := ()) (x := x) (by simp only [hn]),
        buildTree_succ_of_query hn]
      refine congrArg (OracleComp.query (spec := singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)) () x)
        (funext fun y => ?_)
      rw [buildComp_singleCodec next q, toHist_append_singleton]

/-- **The ch. 2–4 decoder is an instance:** the oracle adversary `D.toOracleAdversary` of a
next-query machine is its computation under `singleCodec`. So
`OracleEnsemble.Indist` (via `oracleDist`) is a statement about framework computations. -/
theorem toComp_singleCodec (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) (r : D.Coins n) :
    D.toComp (singleCodec ℓ₁ ℓ₂) n q r =
      D.toOracleAdversary n ℓ₁ ℓ₂ q r := by
  have h := buildComp_singleCodec (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []
  have hnext : (fun hist => (singleCodec ℓ₁ ℓ₂).decodeMove
      (D.runAt n ((singleCodec ℓ₁ ℓ₂).encodeLog hist) r)) =
      (fun h => match decodeOracleMove ℓ₁ (D.runAt n (encodeHist (toHist h)) r) with
        | .query x => Move.query () x
        | .ret b => Move.ret b) := by
    funext hist
    rw [encodeLog_singleCodec, singleCodec_decodeMove]
  rw [NUPPT.toComp_eq, NUPPT.toOracleAdversary_eq, hnext, singleCodec_timeout, h, toHist_nil]

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Bridges/QueryTree.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Query trees in the framework: evaluation, simulation, query bounds

The concrete layer's adaptive oracle adversaries `QueryTree I O α` *are* the `Games` framework's
computations over a single oracle (`QueryTree` abbreviates `OracleComp (singleSpec I O) α`;
ruling of 2026-11-05, item F-1). This file shows that the concrete layer's three operations on
them are the framework's:
- running against an oracle function (`QueryTree.eval`) is evaluating the computation with that
  function (`OracleComp.evalFn`), which is also its simulation by a deterministic stateless
  implementation;
- Garg's `QueryTree.simulate` (answer each query by asking `π x` of a new oracle and
  post-processing with `ans x`) is the framework's `simulate` with the corresponding
  implementation;
- the query bound `QueryTree.BoundedBy` is the framework's `CostBoundedBy` with every query
  costing one.

So the concrete layer's results on oracle adversaries (PRF hybrids, GGM, lazy sampling) are results
about the framework's one-oracle computations. Before the restatement, this file was bridge B1:
a translation between two types, with its inverse and a bijection. The translation is now the
identity and is gone.

## Main definitions

* `Games.OracleComp.evalFn f c`: the output of `c` when every query is answered by the function
  `f`.
* `Games.Bridge.treeImpl π ans`: the implementation corresponding to `QueryTree.simulate π ans`.

## Main results

* `Games.Bridge.eval_eq_evalFn`: evaluation is the framework's.
* `Games.simulate_ofComp_pure`: simulating with a deterministic stateless implementation is
  evaluation.
* `Games.Bridge.simulate_eq`: Garg's simulation is the framework's.
* `Games.Bridge.costBoundedBy_iff_boundedBy`: query bounds are the framework's.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers (`SimSemantics/`).
-/

namespace TCSlib.Cryptography.Games

variable {ι : Type} {I O I' O' α σ : Type}

/-- The output of `c` when every query `x` to oracle `i` is answered by `f i x`. -/
def OracleComp.evalFn {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i) :
    OracleComp spec α → α
  | .pure a => a
  | .query i x k => evalFn f (k (f i x))

/-- A return evaluates to its value: `(pure a).evalFn f = a`. -/
theorem OracleComp.evalFn_pure {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i) (a : α) :
    (OracleComp.pure a : OracleComp spec α).evalFn f = a :=
  rfl

/-- A query evaluates as its continuation on the answer `f i x`:
`(query i x k).evalFn f = (k (f i x)).evalFn f`. -/
theorem OracleComp.evalFn_query {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i)
    (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) :
    (OracleComp.query i x k).evalFn f = (k (f i x)).evalFn f :=
  rfl

/-- **Deterministic implementations evaluate:** simulating `c` with the stateless implementation
that answers by the function `f` returns `c`'s output under `f` and leaves the state unchanged. -/
theorem simulate_ofComp_pure {ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → spec.rng i) (c : OracleComp spec α) (s : σ) :
    simulate (QueryImpl.ofComp (σ := σ) (spec' := spec') fun i x => .pure (f i x)) c s =
      .pure (c.evalFn f, s) := by
  induction c with
  | pure a => rw [simulate_pure, OracleComp.evalFn_pure]
  | query i x k ih =>
    rw [simulate_query, QueryImpl.ofComp_apply, OracleComp.pure_bind, OracleComp.pure_bind,
      OracleComp.evalFn_query]
    exact ih (f i x)

namespace Bridge

/-- **Evaluation is the framework's:** running a tree against the oracle `f` is evaluating it, as
a one-oracle computation, with `f`. -/
theorem eval_eq_evalFn (f : I → O) (t : TCSlib.Cryptography.QueryTree I O α) :
    t.eval f = OracleComp.evalFn (fun _ => f) t := by
  induction t using TCSlib.Cryptography.QueryTree.induct with
  | ret a => rw [TCSlib.Cryptography.QueryTree.eval_ret, OracleComp.evalFn_pure]
  | query x k ih =>
    rw [TCSlib.Cryptography.QueryTree.eval_query, OracleComp.evalFn_query]
    exact ih (f x)

/-- The implementation corresponding to `QueryTree.simulate π ans`: a query `x` is answered by
asking `π x` of the new oracle and returning `ans x` of the answer; no state is used. -/
def treeImpl (π : I → I') (ans : I → O' → O) : QueryImpl (singleSpec I O) σ (singleSpec I' O') :=
  QueryImpl.ofComp fun _ x => (OracleComp.call () (π x)).bind fun o' => .pure (ans x o')

/-- The implementation answers the query `x` by asking `π x` and returning `ans x` of the answer,
with the state `s` unchanged:
`treeImpl π ans u x s = query () (π x) (fun o' => pure (ans x o', s))`. -/
theorem treeImpl_apply (π : I → I') (ans : I → O' → O) (u : Unit) (x : I) (s : σ) :
    treeImpl (σ := σ) π ans u x s = OracleComp.query () (π x) fun o' => .pure (ans x o', s) := by
  rw [treeImpl, QueryImpl.ofComp_apply, OracleComp.bind_assoc, OracleComp.call_bind]
  simp only [OracleComp.pure_bind]

/-- **Garg's simulation is the framework's:** the tree `t.simulate π ans` is the framework's
simulation of `t` by `treeImpl π ans`, with the (unchanged) state dropped.

**Proof sketch.** Induction on `t`; at a query both sides ask `π x` and continue on `ans x` of the
answer. -/
theorem simulate_eq (π : I → I') (ans : I → O' → O) (t : TCSlib.Cryptography.QueryTree I O α)
    (s : σ) :
    t.simulate π ans = (simulate (treeImpl π ans) t s).bind fun p => .pure p.1 := by
  induction t using TCSlib.Cryptography.QueryTree.induct with
  | ret a =>
    rw [TCSlib.Cryptography.QueryTree.simulate_ret, simulate_pure, OracleComp.pure_bind]
  | query x k ih =>
    rw [TCSlib.Cryptography.QueryTree.simulate_query, simulate_query, treeImpl_apply]
    simp only [OracleComp.query_bind, OracleComp.pure_bind, ih]

/-- **Query bounds are the framework's:** a tree makes at most `q` queries exactly when it is
cost-bounded by `q` with every query costing one. -/
theorem costBoundedBy_iff_boundedBy (t : TCSlib.Cryptography.QueryTree I O α) (q : ℕ) :
    OracleComp.CostBoundedBy (fun _ => 1) t q ↔ t.BoundedBy q := by
  induction t using TCSlib.Cryptography.QueryTree.induct generalizing q with
  | ret a => simp
  | query x k ih =>
    cases q with
    | zero => simp [OracleComp.costBoundedBy_query]
    | succ q =>
      simp only [OracleComp.costBoundedBy_query,
        TCSlib.Cryptography.QueryTree.boundedBy_query_succ, Nat.add_sub_cancel, ih]
      simp

end Bridge

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Bridges/Strategies.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Protocols
import TCSlib.Cryptography.ZeroKnowledge.Interaction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bridge B4: next-message strategies as parties

By the ruling of 2026-11-05, the ch. 2–4 layer's next-message strategies
(`TCSlib.Cryptography.Strategy`, executed by `TCSlib.Cryptography.exec` under its decision D8)
remain the definitions of interaction, and the `Games` executor `Party.exec` is the calculus in
which their properties are proved. This file embeds a strategy with a fixed random tape as a
party, and shows that the embedded execution is D8's.

**The embedding.** A strategy's next-message function `next : received ↦ message`, with its common
input, auxiliary input and tape fixed, becomes a party that keeps its received history and the
number of moves left:
- **on its turn** (`turnParty next k M`, with `k` moves left, its own included), it sends `next M`;
- **while waiting** (`waitParty next k M`), it receives the other party's message.
- **When no moves are left,** it returns `next M`: D8's output on the complete history, which for
  the last sender equals its last message (`Protocol.outV_eq_getLast_of_moverIsV`).
- **A reply off schedule** (`none` before the end, `some` after it) returns `next M`, a total
  default. The theorems are about embedded pairs, where it never happens.

**D8's alternation from any state.** `alt nF nG k MF MG` gives the received histories of the
first mover `F` and of `G` after `k` more moves, from `(MF, MG)` with `F` to move.
`exec_eq_alt` identifies D8's `exec` with it.

## Main definitions

* `Games.Bridge.turnParty`, `Games.Bridge.waitParty`: the embedded party on its turn and while
  waiting.
* `Games.Bridge.alt`: D8's alternation from a state.

## Main results

* `Games.Bridge.exec_turnParty`: the execution of two embedded strategies with fuel `k` (the
  number of moves) is `done`, with the outputs `nF` and `nG` on their final histories under `alt`.
* `Games.Bridge.exec_eq_alt`: D8's `exec` is `alt` from the empty histories, with the roles
  ordered by the first mover.
* `Games.Bridge.exec_strategies`: hence the embedded execution of a protocol's two strategies
  returns D8's outputs `outP`, `outV`.

The traced and probabilistic forms (views, and tapes sampled first) are stated in a later part
of this file.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views).
-/

namespace TCSlib.Cryptography.Games.Bridge

open TCSlib.Cryptography

/-- Messages and histories of the ch. 2–4 interaction model. -/
abbrev Msg : Type := List Bool

/-- The embedded party **on its turn**, with `k` moves left in the protocol (its own included)
and received history `M`: it sends `next M`; after its send, `k − 1` moves are left, and it waits.
With no moves left it returns `next M`. -/
def turnParty (next : List Msg → Msg) : ℕ → List Msg → Party Msg Msg Msg
  | 0, M => .pure (next M)
  | k + 1, M => .query (.inl ()) (next M) fun
      | none => .pure (next M)
      | some y => match k with
        | 0 => .pure (next M)
        | k' + 1 => turnParty next k' (M ++ [y])

/-- With no moves left, the embedded party returns `next M`: `turnParty next 0 M = pure (next M)`.
-/
theorem turnParty_zero (next : List Msg → Msg) (M : List Msg) :
    turnParty next 0 M = .pure (next M) :=
  rfl

/-- The embedded party **while waiting**, with `k` moves left (the other party's next one
included) and received history `M`. On the other party's message `y` it takes its turn with
`k − 1` moves left; on `none` (the other party has returned) it returns `next M`. -/
def waitParty (next : List Msg → Msg) (k : ℕ) (M : List Msg) : Option Msg → Party Msg Msg Msg
  | none => .pure (next M)
  | some y => match k with
    | 0 => .pure (next M)
    | k' + 1 => turnParty next k' (M ++ [y])

/-- Waiting, on `none` (the other party has returned), the embedded party returns `next M`. -/
theorem waitParty_none (next : List Msg → Msg) (k : ℕ) (M : List Msg) :
    waitParty next k M none = .pure (next M) :=
  rfl

/-- Waiting with no moves left, a reply off schedule is ignored and the party returns `next M`. -/
theorem waitParty_some_zero (next : List Msg → Msg) (M : List Msg) (y : Msg) :
    waitParty next 0 M (some y) = .pure (next M) :=
  rfl

/-- Waiting with `k + 1` moves left, on the reply `y` the party appends it and takes its turn with
`k` moves left: `waitParty next (k + 1) M (some y) = turnParty next k (M ++ [y])`. -/
theorem waitParty_some_succ (next : List Msg → Msg) (k : ℕ) (M : List Msg) (y : Msg) :
    waitParty next (k + 1) M (some y) = turnParty next k (M ++ [y]) :=
  rfl

/-- On its turn with `k + 1` moves left, the embedded party sends `next M` and then waits with
`k` moves left. -/
theorem turnParty_succ (next : List Msg → Msg) (k : ℕ) (M : List Msg) :
    turnParty next (k + 1) M = .query (.inl ()) (next M) (waitParty next k M) := by
  rw [turnParty]
  congr 1

/-- **D8's alternation from a state:** the received histories of `F` and of `G` after `k` more
moves from `(MF, MG)`, with `F` to move. `F` sends `nF MF`, which `G` receives; then `G` moves. -/
def alt (nF nG : List Msg → Msg) : ℕ → List Msg → List Msg → List Msg × List Msg
  | 0, MF, MG => (MF, MG)
  | k + 1, MF, MG => (alt nG nF k (MG ++ [nF MF]) MF).swap

/-- With no moves left, the histories are unchanged: `alt nF nG 0 MF MG = (MF, MG)`. -/
theorem alt_zero (nF nG : List Msg → Msg) (MF MG : List Msg) : alt nF nG 0 MF MG = (MF, MG) :=
  rfl

/-- `alt`'s step at the front: `F` sends `nF MF` to `G`, then the roles are exchanged:
`alt nF nG (k + 1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap`. -/
theorem alt_succ (nF nG : List Msg → Msg) (k : ℕ) (MF MG : List Msg) :
    alt nF nG (k + 1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap :=
  rfl

/-- `alt`'s step at the back: after `k + 1` moves, the last move is `F`'s when `k` is even (its
message, computed on its history, is appended to `G`'s), and `G`'s when `k` is odd. This is D8's
`exec_succ` shape.

**Proof sketch.** Induction on `k`, generalizing over the two functions and the histories:
`alt`'s step exchanges the roles and the parity of the remaining moves together. -/
theorem alt_succ_last : ∀ (k : ℕ) (nF nG : List Msg → Msg) (MF MG : List Msg),
    alt nF nG (k + 1) MF MG =
      if k % 2 = 0 then ((alt nF nG k MF MG).1, (alt nF nG k MF MG).2 ++ [nF (alt nF nG k MF MG).1])
      else ((alt nF nG k MF MG).1 ++ [nG (alt nF nG k MF MG).2], (alt nF nG k MF MG).2) := by
  intro k
  induction k with
  | zero => intro nF nG MF MG; rfl
  | succ k ih =>
    intro nF nG MF MG
    rw [alt, ih nG nF (MG ++ [nF MF]) MF]
    simp only [alt]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : ¬ (k + 1) % 2 = 0 := by omega
      simp [h, h']
    · have h' : (k + 1) % 2 = 0 := by omega
      simp [h, h']

/-- **Embedded executions are D8's:** with fuel `k`, the number of moves, the execution of `F` on
its turn against `G` waiting returns both outputs, `nF` and `nG` on the final histories of
`alt`.

**Proof sketch.** Induction on `k`, generalizing over the two next-message functions and the
histories.
- With no moves, `F` returns `nF MF`, and `G` is closed with `none` and returns `nG MG`.
- With `k + 1` moves, `exec_succ` and `turnParty_succ` send `nF MF` to `G`, which takes its turn
  with `k` moves left (`waitParty`), against `F` waiting with `k` moves left. The induction
  hypothesis with the roles exchanged, and `ExecOutcome.swap`, give the outputs; `alt`'s step is
  the same exchange. -/
theorem exec_turnParty : ∀ (k : ℕ) (nF nG : List Msg → Msg) (MF MG : List Msg),
    Party.exec k (turnParty nF k MF) (waitParty nG k MG) =
      .pure (.done (nF (alt nF nG k MF MG).1) (nG (alt nF nG k MF MG).2)) := by
  intro k
  induction k with
  | zero =>
    intro nF nG MF MG
    simp only [turnParty_zero, Party.exec_zero, Party.step_pure, OracleComp.pure_bind,
      Sum.elim_inl, Party.endWith_eq, waitParty_none, Party.close_pure, Option.elim_some,
      alt_zero]
  | succ k ih =>
    intro nF nG MF MG
    simp only [turnParty_succ, Party.exec_succ, Party.step_send, OracleComp.pure_bind,
      Sum.elim_inr, waitParty_some_succ, ih, ExecOutcome.swap_done, alt_succ, Prod.fst_swap,
      Prod.snd_swap]

/-- **D8's `exec` is `alt`:** after `k` moves from the empty histories, the messages received by
`P` and by `V` are `alt`'s, with the first mover chosen by `vFirst`.

**Proof sketch.** Generalize to `j + k` moves: D8's state after `j` moves, continued by `alt`
for `k` more with the mover at position `j` (`moverIsV`), is D8's state after `j + k` moves.
Induct on `k`; the parity of `j` decides who moves, and `exec_succ` (D8's) appends the message
to the other party's list exactly as `alt`'s step does. -/
theorem exec_eq_alt (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vFirst x zP zV rP rV k =
      if vFirst then (alt (V.next x zV rV) (P.next x zP rP) k [] []).swap
      else alt (P.next x zP rP) (V.next x zV rV) k [] [] := by
  induction k with
  | zero =>
    cases vFirst <;>
      simp only [exec_zero, alt_zero, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk]
  | succ k ih =>
    rw [exec_succ, ih]
    cases vFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [alt_succ_last] <;>
      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [moverIsV_true, moverIsV_false, h]

/-- **A protocol's embedded execution returns D8's outputs:** for fixed tapes, running the first
mover's embedding on its turn against the other's waiting embedding, with fuel the number of
messages, returns the prover's and the verifier's D8 outputs (`Protocol.outP`,
`Protocol.outV`), in the first mover's order.

**Proof sketch.** `exec_turnParty` with `k = π.rounds.eval |x|` and the next-message functions of
the two strategies, then `exec_eq_alt` with `π.transcriptWith`'s unfolding; `outP` and `outV`
are the next-message functions on the final histories. -/
theorem exec_strategies (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    Party.exec (π.rounds.eval x.length)
        (turnParty (if π.verifierFirst then π.V.next x z (List.ofFn r.2)
          else π.P.next x y (List.ofFn r.1)) (π.rounds.eval x.length) [])
        (waitParty (if π.verifierFirst then π.P.next x y (List.ofFn r.1)
          else π.V.next x z (List.ofFn r.2)) (π.rounds.eval x.length) []) =
      .pure (if π.verifierFirst then .done (π.outV π.P x y z r) (π.outP x y z r)
        else .done (π.outP x y z r) (π.outV π.P x y z r)) := by
  have hT := exec_eq_alt π.P π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
    (π.rounds.eval x.length)
  simp only [Protocol.outP_eq, Protocol.outV_eq, Protocol.transcriptWith_eq]
  cases hv : π.verifierFirst
  · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hT ⊢
    rw [exec_turnParty, hT]
  · simp only [hv, ↓reduceIte] at hT ⊢
    rw [exec_turnParty, hT, Prod.fst_swap, Prod.snd_swap]

end TCSlib.Cryptography.Games.Bridge

## ===== TCSlib/Cryptography/Games/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficiency of reductions (skeleton for the efficiency fill)

A reduction runs a machine adversary `A` and answers `A`'s queries with a polynomial-time
**handler**. Proved once, the targets below say that the result is again a machine, so the
hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The route is
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`. The template is Frederick Dehmel's GGM
reduction machine (`Asymptotic/GGMReduction*.lean`), whose loop `GGMRed.stateLoopFun` is reused.

**Status: skeleton.** The definitions (T0) are final. The statements of T1, T2 and T4 and of the
companion `exists_toCompOn_of_toComp` are frozen at the issue of the fill brief
(`briefs/pass-shelat-ch5-8/fills/efficiency/`). Their proofs are the fill's.

## The shape of a reduction

A handler describes everything a reduction does around one run of the adversary. At parameter
`n` the reduction has an input `z` and a seed `ω` (its own coins). Every function of the handler
reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`):
1. **the adversary's input** is a polynomial-time function of the context (`advIn`), for example
   a public key built from `z` and `ω`; the adversary runs as `A.toCompOn` on it;
2. **each query** of the adversary is answered from the handler's state, by the handler alone
   (`PolyHandler`) or with queries to the reduction's own oracles (`InteractiveHandler`);
3. **the reduction's output** is computed from the context, the final state and the adversary's
   output: by a polynomial-time function (`PolyHandler.out`), or by a last phase that may itself
   query the reduction's oracles, within its own budget (`InteractiveHandler.finish`).

## Fixed lengths

Every length is an explicit polynomial in the parameter `n`: queries and answers (`din i`,
`dout i`), the adversary's output (`dα`), the handler's state and seed, and, for an interactive
handler, the reduction's output. This bounds every history, which the guarded state loop needs.

## Scope

* **Covered:** a reduction that runs one adversary once, on an input computed from its own,
  answers the adversary's queries with or without its own oracles, and post-processes the final
  state and the adversary's output (with further oracle queries if it is interactive). T1 makes
  the machine's output exactly the finalized output; T2 makes the machine's computation exactly
  the simulation followed by the finalization, with the budgets added.
* **Adversaries without input** are adversaries with an input they ignore
  (`exists_toCompOn_of_toComp`).
* **Reductions to a pseudorandom function** reach `OracleEnsemble.Indist` through T4: an oracle
  machine against one bit-string oracle with a one-bit output is, on evaluations, a next-query
  machine of the ch. 2–4 layer (`NUPPT.toOracleAdversary`).
* **Non-uniform handlers** (for example one that runs a non-uniform distinguisher) receive their
  advice through the input `z`; it is hard-wired into the machine afterwards
  (`NUPPT.exists_withAdvice`, with `NUPPT.exists_comp` to re-pair the input).
* **Not covered:** reductions that rewind the adversary or run it more than once, and variable
  lengths.

## Main definitions

* `Games.seedIn n z ω`: the context `⟨1^n, ⟨z, ω⟩⟩`.
* `Games.PolyHandler k din dout`: a polynomial-time handler for `k` bit-string oracles, with its
  state and seed lengths, initial state, adversary input and finalization.
* `Games.PolyHandler.answer`, `Games.PolyHandler.impl`: its answers, and its semantics as a
  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`;
  `PolyHandler.advInput` and `PolyHandler.result`: the adversary's input and the reduction's
  output.
* `Games.InteractiveHandler`, `InteractiveHandler.call`, `InteractiveHandler.impl`: a
  polynomial-time handler that may itself query outer bit-string oracles, up to `perCall(n)`
  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
  `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
  finalization, with up to `finCall(n)` outer queries.

## Main results

* `Games.exists_handlerMachine` (T1, the fill's target): a reduction with a polynomial-time
  handler is a machine, whose output is exactly the finalized output of the simulation.
* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a reduction with an
  interactive handler is an oracle machine against the outer oracles, with budget
  `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
  finalization. The reductions that forward or answer queries with their own oracle need it (the
  PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
* `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
  with an input that it ignores, with the same coins.
* `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
  against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
  next-query machine of the ch. 2–4 layer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  every reduction of ch. 5–8 (for example the proofs of Thms 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- The bit-string oracles at parameter `n`, with polynomial lengths. -/
abbrev bitSpecAt (din dout : Fin k → PolyExpr) (n : ℕ) : OracleSpec (Fin k) :=
  bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)

/-- The bit-string oracles at parameter `n` are `bitSpec` of the evaluated lengths:
`bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)`. -/
theorem bitSpecAt_eq (din dout : Fin k → PolyExpr) (n : ℕ) :
    bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n) :=
  rfl

/-- The **context** of a reduction at parameter `n`, with the reduction's input `z` and its seed
`ω`: the string `⟨1^n, ⟨z, ω⟩⟩`. Every function of a handler reads it. -/
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)

/-- The context is `⟨1^n, ⟨z, ω⟩⟩`:
`seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω)`. -/
theorem seedIn_eq (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) :=
  rfl

/-- A **polynomial-time handler** for `k` bit-string oracles with query lengths `din` and answer
lengths `dout`: a reduction that runs the adversary once and answers its queries by itself. Its
three functions are polynomial-time, and each reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the
parameter, the reduction's input `z` and its seed `ω`):
- `advIn` maps the context to the adversary's input;
- `run` answers one query: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the context, the state `s`, and
  the query `x` to oracle `i`), it returns `⟨y, s'⟩`, the answer and the new state;
- `out` maps `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the context, the final state and the adversary's output)
  to the reduction's output. -/
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed (the handler's own coins). -/
  seedLen : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- The handler as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩` (for example a public
  key built from `z` and the seed). For an adversary without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The finalization: the reduction's output, as a function of `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the
  context, the final state `s` and the adversary's output `a`). -/
  out : List Bool → List Bool
  /-- The finalization is polynomial-time computable. -/
  out_poly : PolyTimeComputable out

namespace PolyHandler

variable {din dout : Fin k → PolyExpr}

/-- The handler's input string for the query `x` to oracle `i` in state `s`. -/
def input (n : ℕ) (z : List Bool) (ω : List Bool) (s : List Bool) (i : Fin k) (x : List Bool) :
    List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (List.replicate i true) x))

/-- The handler's input string is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    input n z ω s i x =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (List.replicate i true) x)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- The reduction's output at parameter `n`, for the reduction input `z` and the seed `ω`, when
the final state is `s` and the adversary's output is `a`: `out` of
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`. -/
def result (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : List Bool :=
  H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a)))

/-- The reduction's output is `out` of the context, the final state and the adversary's output:
`H.result n z ω s a = H.out (pairEncode (seedIn n z (List.ofFn ω))
(pairEncode (List.ofFn s) (List.ofFn a)))`. -/
theorem result_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.result n z ω s a =
      H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a))) :=
  rfl

/-- The handler's answer and new state, decoded with fixed lengths. If `run`'s output is not a
pair, both are all-`false`; otherwise each component of the wrong length is replaced by
all-`false` independently (a total default; well-behaved handlers never produce one). An
interactive handler defaults jointly instead (`InteractiveHandler`). -/
def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    (Fin ((dout i).eval n) → Bool) × (Fin (H.stateLen.eval n) → Bool) :=
  match pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) with
  | some (yw, sw) =>
    ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
  | none => (zeroBits _, zeroBits _)

section Answer

variable (H : PolyHandler k din dout) {n : ℕ} {z : List Bool} {ω : Fin (H.seedLen.eval n) → Bool}
  {s : Fin (H.stateLen.eval n) → Bool} {i : Fin k} {x : Fin ((din i).eval n) → Bool}

/-- If `run`'s output is not a pair, the answer and the new state are all-`false`. -/
theorem answer_of_pairDecode_eq_none
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) = none) :
    H.answer n z ω s i x = (zeroBits _, zeroBits _) := by
  unfold answer
  rw [h]

/-- If `run`'s output is the pair `⟨yw, sw⟩`, the answer is `yw` and the new state `sw`, each
decoded with its fixed length and all-`false` if that length is wrong:
`H.answer n z ω s i x = ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`.
-/
theorem answer_of_pairDecode_eq_some {yw sw : List Bool}
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (yw, sw)) :
    H.answer n z ω s i x =
      ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _)) := by
  unfold answer
  rw [h]

/-- **A well-formed output:** if `run` returns `⟨y, s'⟩` with `y` and `s'` of the fixed lengths,
the answer is `y` and the new state `s'`. -/
theorem answer_of_run_eq {y : Fin ((dout i).eval n) → Bool} {s' : Fin (H.stateLen.eval n) → Bool}
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn s')) :
    H.answer n z ω s i x = (y, s') := by
  have h' : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (List.ofFn y, List.ofFn s') := by
    rw [h, pairDecode_pairEncode]
  rw [answer_of_pairDecode_eq_some H h', decodeFin_ofFn, decodeFin_ofFn, Option.getD_some,
    Option.getD_some]

end Answer

/-- The handler as an implementation of the bit-string oracles at parameter `n`, for the
reduction input `z` and seed `ω`: it keeps its state and asks no oracle (the non-interactive
case). -/
def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
  fun i x s => .pure (H.answer n z ω s i x)

/-- The handler answers the query `x` to oracle `i` in state `s` with no coins and no queries:
`H.impl n z ω i x s = pure (H.answer n z ω s i x)`. -/
theorem impl_apply (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s = .pure (H.answer n z ω s i x) :=
  rfl

end PolyHandler

/-- **T1 (the efficiency fill's target; non-interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and a polynomial-time
handler `H`, there is a machine `B` and, at every parameter, a bijection `φ` from (the handler's
seed, `A`'s coins) to `B`'s coins, with the following property. Run `A` on the input
`H.advInput n z ω`, answer its queries by `H` (input `z`, seed `ω`) from `H`'s initial state, and
let `a` be `A`'s output and `s` the final state. Then `B`'s output on input `z` with coins
`φ (ω, r)` is exactly the reduction's output `H.result n z ω s a`.

**Proof sketch** (the fill's; route note §"The route", steps 1–4 without the log replay):
1. `B`'s first step computes `A`'s input `H.advIn (seedIn n z ω)` (polynomial-time by
   `H.advIn_poly`; so its length is polynomial in `n + |z|`), and keeps it in the loop state.
2. `B`'s round function, on `⟨1^n, z, ω, r, A's input, history, state⟩`, runs `A`'s next-move
   function on `⟨A's input, encoded history⟩` (`NUPPT.polyTimeComputable_output`), decodes the
   move (`decodeBitMove`, read through `decodeBitMove_eq_query_iff` and
   `decodeBitMove_of_not_canonical`), and either feeds the query to `H.run` (polynomial-time by
   `H.poly`), appending the answer and the new state, or stops with `A`'s output and the state.
3. `GGMRed.stateLoopFun` runs at most `q(n) + 1` rounds; `stateLoopFun_poly` makes it
   polynomial-time, given that the histories stay below a polynomial (all lengths are fixed).
   The loop's result `(a, s)` is finalized by `H.out` on `⟨seedIn n z ω, ⟨s, a⟩⟩`
   (polynomial-time by `H.out_poly`).
4. `B := NUPPT.ofPolyTime` of the composite, with the coins split as `(ω, r)` by `exists_split`
   (`Complexity/Randomized/Closure.lean`).
5. The functional equation: by induction on the remaining budget, the loop's state after `t`
   rounds is the simulation's state after `t` queries (`toCompOn_eq` and `buildComp`'s case
   lemmas against `simulate_query`, `PolyHandler.impl_apply` and the `answer` lemmas);
   `stateLoopFun_eval` reads off `(a, s)`, and `result_eq` the output. -/
theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
    (dα : PolyExpr) (H : PolyHandler k din dout) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
          simulate (H.impl n z ω)
              (A.toCompOn
                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
  sorry

/-! ### Interactive handlers (T2) -/

variable {k' : ℕ}

/-- A **polynomial-time interactive handler** for `k` inner bit-string oracles that may itself
query `k'` outer bit-string oracles. Like `PolyHandler`, it computes the adversary's input from
the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queries (`run`), and computes the
reduction's output in a last phase (`finRun`), both with outer queries.

One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
`perCall(n) + 1` rounds of `run` (the last returns the answer or, with the budget spent, is cut off
with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
joint default, unlike `PolyHandler.answer`, which defaults each component separately).

The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
output on a malformed round output or a spent budget. -/
structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
    (din' dout' : Fin k' → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The bound on outer queries per inner query. -/
  perCall : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- One round of the handler, as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩`. For an adversary
  without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The length of the reduction's output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- One round of the finalization, as a string function: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` it
  returns an outer query `⟨[false], ⟨1^j, x'⟩⟩` or the reduction's output `⟨[true], b⟩`. -/
  finRun : List Bool → List Bool
  /-- The finalization's round is polynomial-time computable. -/
  finRun_poly : PolyTimeComputable finRun

namespace InteractiveHandler

variable {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- The handler's input string for one round. -/
def input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L))

/-- The handler's input string for one round is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    input n z ω s i x L =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
`perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
is the all-`false` answer and state (`decodeBitMove`'s default), and so is an exhausted budget. -/
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []

/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
`perCall(n)` and the all-`false` result when it runs out: `H.call n z ω s i x =
buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
-/
theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    H.call n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + H.stateLen.eval n)
          (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.perCall.eval n) [] :=
  rfl

/-- The interactive handler as an implementation of the inner oracles by the outer ones, at
parameter `n`, reduction input `z` and seed `ω`: one `call` per inner query, its result split
into the answer and the new state. -/
def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) (bitSpecAt din' dout' n) :=
  fun i x s => (H.call n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))

/-- The inner query `x` to oracle `i` in state `s` is answered by one `call`, whose result is
split into the answer (its first `dout i` bits) and the new state (the rest):
`H.impl n z ω i x s = (H.call n z ω s i x).bind fun w =>
pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))`. -/
theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s =
      (H.call n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
  rfl

/-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
  pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))

/-- The input string of one round of the finalization is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
`finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))`. -/
theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
    finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
  rfl

/-- **The finalization** in the final state `s`, after the adversary's output `a`: the
reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
`finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
(`decodeBitMove`'s default), and so is an exhausted budget. -/
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []

/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
`finCall(n)` and the all-`false` output when it runs out: `H.finish n z ω s a =
buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
(H.finCall.eval n) []`. -/
theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.finish n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (H.outLen.eval n)
          (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.finCall.eval n) [] :=
  rfl

end InteractiveHandler

/-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and an interactive
handler `H` answering them through `k'` outer oracles, there is an oracle machine `B` against the
outer oracles, with budget `q(n) · perCall(n) + finCall(n)`, and at every parameter a bijection
`φ` from (`H`'s seed, `A`'s coins) to `B`'s coins, with the following property. `B` on input `z`
with coins `φ (ω, r)` is, as an oracle computation, exactly the reduction: `A` run on the input
`H.advInput n z ω`, its queries answered by `H` (input `z`, seed `ω`) from `H`'s initial state,
followed by `H`'s finalization on the final state and `A`'s output.

**Proof sketch** (the fill's; route note §"The route", with the log replay).
1. `B`'s next-move function, on `⟨z, outer log⟩` with coins `(ω, r)`, first computes `A`'s input
   `H.advIn (seedIn n z ω)` (`H.advIn_poly`). It then replays: it splits the outer log into the
   calls of `H` and the finalization. Within each call it reruns `H.run` round by round, and
   between calls it reruns `A`'s next-move function on `⟨A's input, inner log⟩`, the inner log
   rebuilt from the calls' answers. Once `A` returns `a` (or meets its own budget), it reruns
   `H.finRun` on `⟨seedIn n z ω, ⟨s, ⟨a, L⟩⟩⟩` with the rest `L` of the log. It stops at the first
   pending outer query (and asks it) or at the finalization's output (and returns its canonical
   word, `encodeBitMove`). Every length is fixed, so each replay is polynomial
   (`stateLoopFun_poly`, as in T1).
2. `B`'s budget suffices: each of `A`'s at most `q(n)` queries costs at most `perCall(n)` outer
   queries and the finalization at most `finCall(n)` (`buildComp_costBoundedBy`,
   `simulate_costBoundedBy`, `CostBoundedBy.bind`), so `B` never meets its own timeout before
   the reduction ends, and it mirrors every default of `A`, of a call and of the finalization.
3. The functional equation: by induction on the outer log, the two computation trees agree node
   by node (`simulate_query`, `impl_apply`, `call_eq`, `finish_eq`, `toCompOn_eq`, `buildComp`'s
   case lemmas, `decodeBitMove_encodeBitMove`). Coins split as `(ω, r)` by `exists_split`. -/
theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
    (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
    (H : InteractiveHandler k din dout k' din' dout') :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        (simulate (H.impl n z ω)
            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
            (fun res => H.finish n z ω res.2 res.1) =
          B.toCompOn
            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
  sorry

/-! ### Companions: adversaries without input, and the bridge to pseudorandom functions (T4) -/

/-- **A machine without input is a machine with an input that it ignores.** For every machine
`A` there is a machine `A'` with the same coins whose computation on any input `x` is `A`'s
computation, for every codec and budget, the coins related by a bijection `φ`. So T1 and T2,
stated for adversaries with input, cover adversaries without one.

**Proof sketch.** `A'` is `NUPPT.exists_comp` of `A` with `pre = pairSndD` and `post = id`, so
`A'.coins = A.coins` and `A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). The
bijection `φ` transports the coins along `A.coinLen n = A'.coinLen n` (`finCongr`), so
`List.ofFn (φ r) = List.ofFn r` (`List.ofFn_congr`); with `runAt_eq` the next-move functions of
`A'.toCompOn codec n q x (φ r)` and `A.toComp codec n q r` agree on every log, and
`toCompOn_eq`, `toComp_eq` conclude. The length equation needs an equation of `NUPPT.coinLen`,
published beside its definition. -/
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  sorry

/-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
machine `B'` with the same coins whose oracle adversary `B'.toOracleAdversary`, run against any
`f`, returns the bit of `B`'s computation evaluated with `f`, the coins related by a bijection
`φ`. So `OracleEnsemble.Indist`, and with it `PRF`, applies to the machines of T2 with one outer
oracle and a one-bit output (through `oracleDist_apply` and `Bridge.eval_eq_evalFn`).

**Proof sketch.**
1. `B'` translates between the two formats around `B` (`NUPPT.exists_comp` with polynomial-time
   pre- and post-processing, or `NUPPT.ofPolyTime` of the composite to read `1^{ℓ₁(n)}`):
   - its input, the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`), becomes `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩,
     ⟨…, []⟩⟩⟩`, `B`'s empty input and its log (`encodeHist_cons`, `encodeLog_cons`,
     `bitCodec_encodeEntry` with `1^0 = []`), polynomial-time by iterating over the pairs;
   - `B`'s output, a move decoded by `decodeBitMove` (`decodeBitMove_eq_query_iff`,
     `decodeBitMove_of_not_canonical`, `decodeIdx_eq_some_iff` at `k = 1`), becomes the query
     `⟨[false], x⟩` for a query `x`, and the verdict `[true, b]` for an output `[b]` and for the
     default.
2. Both trees branch on corresponding moves, so by induction on the budget
   (`toOracleAdversary_eq` and `buildTree`'s case lemmas against `toCompOn_eq` and `buildComp`'s)
   their evaluations against `f` and `fun _ => f` agree (`QueryTree.eval_query`,
   `OracleComp.evalFn_query`); at the timeout the verdict `false` is bit `0` of `zeroBits 1`
   (`zeroBits_apply`).
3. `φ` transports the coins along `B.coins = B'.coins`, as in `exists_toCompOn_of_toComp`. -/
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Hopping.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Game hopping

The steps of a game-based security proof, proved once:
- **the difference lemma**: two events that agree unless a "bad" event happens differ in
  probability by at most the probability of the bad event;
- **identical until bad**: two oracle implementations that give the same law to good successors
  until a flag in their state is raised, and never lower it, give simulations whose outputs differ
  in probability by at most the probability that the flag is raised;
- **a collision bound**: one fresh uniform sample lands in a list of at most `q` values fixed
  before it with probability at most `q / |T|`. The adaptive repeated-nonce event of
  [PS10, Thm 168.2] (later nonces hitting an earlier one) is a union of such steps; its lemma is
  scheduled with the statement phase.

The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Advantage`).

## Main definitions

* `Games.OracleComp.AllOutputs P c` (in `TCSlib.Cryptography.Games.OracleComp`): every possible
  output of `c` satisfies `P`.

## Main results

* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
  possible outputs only.
* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, §1.1, Lemma 1].
* `ProbComp.prob_mem_le`: the collision bound.
* `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
  code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
  state; `Games.hagree_of_eq` recovers the syntactic hypothesis.

## References

* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006; full version IACR ePrint 2004/331 (the
  fundamental lemma of game playing).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332, revision of 18 January 2006 (https://www.shoup.net/papers/games.pdf),
  §1.1, Lemma 1 (the difference lemma).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Thm 168.2 (proof sketch: the bad events of the CPA analysis).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset

variable {ι : Type} {α β σ : Type}

namespace ProbComp

/-- An event splits by a second event: `Pr[A] = Pr[A ∧ ¬F] + Pr[A ∧ F]`. -/
theorem prob_split (c : ProbComp α) (A F : α → Prop) :
    prob c A = prob c (fun a => A a ∧ ¬ F a) + prob c (fun a => A a ∧ F a) := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  congr 1
  funext a
  by_cases hA : A a <;> by_cases hF : F a <;> simp [hA, hF]

/-- If every possible output of `c` satisfies `P`, and `f ≤ g` at every output satisfying `P`,
then the expectation of `f` over `c` is at most that of `g`. -/
theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
  induction c with
  | pure a =>
    rw [expect_pure, expect_pure]
    exact h a (OracleComp.allOutputs_pure.1 hc)
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left
      (sum_le_sum fun j _ => ih j (OracleComp.allOutputs_query.1 hc j)) (by positivity)

/-- An event holding at every possible output has probability one. -/
theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
    prob c p = 1 := by
  classical
  refine le_antisymm (prob_le_one c p) ?_
  rw [prob_eq_expect]
  calc (1 : ℝ) = expect c (fun _ => 1) := (expect_const c 1).symm
    _ ≤ _ := expect_mono_of_allOutputs hc fun a ha => by simp [ha]

/-- An event failing at every possible output has probability zero. -/
theorem prob_eq_zero_of_allOutputs {c : ProbComp α} {p : α → Prop}
    (hc : c.AllOutputs fun a => ¬ p a) : prob c p = 0 := by
  have h := prob_not c p
  rw [prob_eq_one_of_allOutputs hc] at h
  linarith

/-- **The difference lemma:** if the events `A` and `B` agree at every output where `F` fails,
their probabilities differ by at most the probability of `F`. [Sho04, §1.1, Lemma 1]

**Proof sketch.** Pointwise, the indicators of `A` and `B` differ by at most the indicator of
`F`; take expectations in both directions (linearity and monotonicity). -/
theorem abs_prob_sub_le_of_agree (c : ProbComp α) {A B F : α → Prop}
    (h : ∀ a, ¬ F a → (A a ↔ B a)) : |prob c A - prob c B| ≤ prob c F := by
  classical
  have key : ∀ (A B : α → Prop), (∀ a, ¬ F a → (A a ↔ B a)) →
      prob c A ≤ prob c B + prob c F := by
    intro A B hAB
    rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
    exact expect_mono c fun a => by
      by_cases hF : F a
      · by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB, hF]
      · have := hAB a hF
        by_cases hA : A a
        · simp [hA, this.1 hA, hF]
        · simp [hA, hF]; split_ifs <;> norm_num
  rw [abs_le]
  constructor
  · linarith [key B A fun a ha => (h a ha).symm]
  · linarith [key A B h]

/-- **The collision bound:** if every possible output list has length at most `q`, one fresh
uniform element of `T`, drawn after the list, lies in it with probability at most `q / |T|`.
A standard union-bound fact behind the bad events of [PS10, Thm 168.2]'s proof sketch; the
adaptive repeated-nonce event is a union of such steps.

**Proof sketch.** By total probability over the list, it suffices that a fixed list `L` of length
at most `q` is hit with probability `#{t ∈ L} / |T| ≤ q / |T|`; average over the possible lists
with `expect_mono_of_allOutputs`. -/
theorem prob_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (c : ProbComp (List T))
    {q : ℕ} (hc : c.AllOutputs fun L => L.length ≤ q) :
    prob (c.bind fun L => (sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1) ≤
      q / Fintype.card T := by
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [prob_bind]
  calc expect c (fun L => prob ((sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1))
      ≤ expect c (fun _ => (q : ℝ) / Fintype.card T) := by
        refine expect_mono_of_allOutputs hc fun L hL => ?_
        rw [prob_bind, expect_sample]
        have hsum : ∑ t : T, prob (OracleComp.pure (L, t)) (fun p : List T × T => p.2 ∈ p.1) =
            (L.toFinset.card : ℝ) := by
          simp only [prob_pure, Finset.sum_boole]
          congr 2
          ext t
          simp
        rw [hsum, inv_mul_eq_div]
        refine div_le_div_of_nonneg_right ?_ hT.le
        exact_mod_cast (List.toFinset_card_le L).trans hL
    _ = q / Fintype.card T := expect_const c _

end ProbComp

/-- From a bad state, every possible final state of the simulation is bad, when the
implementation never leaves a bad state. -/
theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) (hstick : ∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) {s : σ} (hs : bad s) :
    (simulate impl c s).AllOutputs fun r => bad r.2 := by
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, OracleComp.allOutputs_pure]
    exact hs
  | query i x k ih =>
    rw [simulate_query]
    exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys

/-- Splitting an expectation on a predicate: on `b` the function is `1`, elsewhere `f`. -/
private theorem expect_ite_one_split {γ : Type} (c : ProbComp γ) (b : γ → Prop) [DecidablePred b]
    (f : γ → ℝ) :
    ProbComp.expect c (fun y => if b y then 1 else f y) =
      (1 - ProbComp.expect c (fun y => if b y then 0 else 1)) +
        ProbComp.expect c (fun y => if b y then 0 else f y) := by
  have h : (fun y => if b y then (1 : ℝ) else f y) =
      fun y => (1 + (-1) * (if b y then (0 : ℝ) else 1)) + (if b y then 0 else f y) := by
    funext y
    by_cases hy : b y <;> simp [hy]
  rw [h, ProbComp.expect_add c (fun y => 1 + (-1) * (if b y then (0 : ℝ) else 1))
      (fun y => if b y then 0 else f y),
    ProbComp.expect_add c (fun _ => (1 : ℝ)) (fun y => (-1) * (if b y then (0 : ℝ) else 1)),
    ProbComp.expect_const, ProbComp.expect_const_mul]
  ring

/-- **Equal until bad:** let two implementations give, from every good state, the same law to good
successors (they may differ arbitrarily on bad successors, including in the call that makes the
state bad), and let each keep bad states bad. Then, from a good state, the two simulations give
the same probability to "`Q` holds and the final state is good", and the same probability to "the
final state is bad".

**Proof sketch.** Induction on the computation. At a query from a good state, write `F_b` for the
continuation's probability of the event. On a bad successor `F_b` is `0` (for "good at the end")
or `1` (for "bad at the end") on both sides (`simulate_allOutputs_bad`). So each expectation only
depends on `F_b` at good successors, where `F₀ = F₁` by induction; and the two implementations give
good successors the same law (`hagree`, once with `g := F₁` and once with `g := 1`). -/
theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (Q : α → Prop) {s : σ} (hs : ¬ bad s) :
    ProbComp.prob (simulate impl₀ c s) (fun r => Q r.1 ∧ ¬ bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => Q r.1 ∧ ¬ bad r.2) ∧
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
  induction c generalizing s with
  | pure a => simp only [simulate_pure, and_self]
  | query i x k ih =>
    simp only [simulate_query, ProbComp.prob_bind]
    constructor
    · -- "`Q` and good at the end"
      have h0 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
            if bad ys.2 then 0 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr)
        · rw [if_neg hb]
          exact (ih ys.1 hb).1
      have h1 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
            if bad ys.2 then 0 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)
        · rw [if_neg hb]
      rw [funext h0, hagree i x s hs, ← funext h1]
    · -- "bad at the end"
      have h0 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => bad r.2) =
            if bad ys.2 then 1 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb)
        · rw [if_neg hb]
          exact (ih ys.1 hb).2
      have h1 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) =
            if bad ys.2 then 1 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)
        · rw [if_neg hb]
      rw [funext h0, expect_ite_one_split, hagree i x s hs (fun _ => 1), hagree i x s hs,
        ← expect_ite_one_split, ← funext h1]

/-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
same oracles give, from every good state, the same law to good successors, and let each keep `bad`
once it holds (every possible new state of a bad state is bad). Then, from a good state, for any
computation `c` and event `p` on its output, the probabilities of `p` under the two simulations
differ by at most the probability that the first simulation ends in a bad state.
[BR06] (the fundamental lemma)

**Deviation:** [BR06] assumes the two games' code is syntactically identical up to `bad ← true`.
Here the hypothesis is semantic: from a good state the two implementations give the same law to
good successors, and may differ arbitrarily on bad ones, including in the call that raises the
flag. Stickiness is required; without it the bound fails.

**Proof sketch.**
1. *Sticky:* from a bad state, every possible final state of either simulation is bad
   (`simulate_allOutputs_bad`).
2. *Equal until bad:* `prob_eq_until_bad`.
3. Write each probability of `p` as "`p` and good" plus at most "bad", and conclude with the
   difference lemma's arithmetic. -/
theorem identical_until_bad {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) {s : σ} (hs : ¬ bad s) :
    |ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) := by
  obtain ⟨h1, h2⟩ := prob_eq_until_bad bad hagree hstick₀ hstick₁ c p hs
  rw [ProbComp.prob_split (simulate impl₀ c s) (fun r => p r.1) (fun r => bad r.2),
    ProbComp.prob_split (simulate impl₁ c s) (fun r => p r.1) (fun r => bad r.2), h1]
  have a0 := ProbComp.prob_nonneg (simulate impl₀ c s) (fun r => p r.1 ∧ bad r.2)
  have a1 := ProbComp.prob_nonneg (simulate impl₁ c s) (fun r => p r.1 ∧ bad r.2)
  have b0 := ProbComp.prob_mono (simulate impl₀ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  have b1 := ProbComp.prob_mono (simulate impl₁ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  rw [abs_le]
  constructor <;> linarith

/-- Equal implementations on good states give the same law to good successors: the hypothesis of
`identical_until_bad` in its syntactic form. -/
theorem hagree_of_eq {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad] (h : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s) :
    ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys) :=
  fun i x s hs _ => by rw [h i x s hs]

/-- **Identical until bad, from a sampled initial state:** if every possible initial state is
good, the bound of `identical_until_bad` holds for the games that first sample the state.

**Proof sketch.** Total probability over the initial state, the pointwise bound at every possible
(good) initial state (`identical_until_bad`), and monotonicity and linearity of expectation. -/
theorem identical_until_bad_init {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) (init : ProbComp σ)
    (hinit : init.AllOutputs fun s => ¬ bad s) :
    |ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (init.bind fun s => simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => bad r.2) := by
  rw [ProbComp.prob_bind, ProbComp.prob_bind, ProbComp.prob_bind]
  have key := fun s (hs : ¬ bad s) =>
    abs_le.1 (identical_until_bad bad hagree hstick₀ hstick₁ c p hs)
  have u := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).2])
  have v := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).1])
  rw [ProbComp.expect_add] at u v
  rw [abs_le]
  constructor <;> linarith

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Complexity.Randomized.PPT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as oracle computations

The asymptotic layer quantifies over non-uniform probabilistic polynomial-time machines
(`Complexity.NUPPT`). A machine interacts with oracles as a **next-move function**: at
parameter `n`, with one random tape `r` for the whole interaction, it is run on the encoding of the
queries and answers so far. Its output is decoded as the next move: a query to one of the
oracles, or the final output. A query budget `q` ends the interaction (D7 of the ch. 2–4 design:
no oracle tapes, one activation per query).

This file turns such a machine into an oracle computation of the `Games` framework
(`NUPPT.toComp`), for any oracle family and any output type, given a *codec*: how output strings
decode into moves, and how a query-log entry encodes as a string. It needs only the machine model
and the framework, so the asymptotic layer can build on it. The ch. 2–4 layer's
`NUPPT.toOracleAdversary` (one oracle, a Boolean verdict) is the instance with the codec built
from its own `decodeOracleMove` and `encodeHist` (`TCSlib.Cryptography.Games.Bridges.Machines`).

The efficiency counterpart (a reduction written as an implementation of polynomial-time
computable handlers, run on a machine, is again a machine's computation) is the S2b efficiency
result, stated in a later module.

## Main definitions

* `Games.Move spec α`: a query to an oracle of `spec`, or a final output in `α`.
* `Games.MachineCodec spec α`: decoding of moves and encoding of log entries.
* `Games.buildComp next timeout q hist`: the computation of a next-move function with budget `q`.
* `Complexity.NUPPT.toComp D codec n q r`: the computation of the machine `D` at parameter `n`
  with coins `r`; `Complexity.NUPPT.toCompOn D codec n q x r`, the same on the input `x`.

## Main results

* `Games.buildComp_costBoundedBy`, `NUPPT.toComp_costBoundedBy`: the computation makes at most `q`
  queries.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 and Definition 96.1 (oracle machines).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {ι : Type} {α : Type}

/-- A **move** of a next-move machine against the oracles of `spec`: ask oracle `i` the query
`x`, or stop with the output `a`. -/
inductive Move (spec : OracleSpec ι) (α : Type) : Type where
  /-- Ask oracle `i` the query `x`. -/
  | query (i : ι) (x : spec.dom i)
  /-- Stop with the output `a`. -/
  | ret (a : α)

/-- A **codec** for machines against `spec` with outputs in `α`: how an output string decodes
into a move, how one query-log entry is encoded for the machine, and the output forced when the
query budget runs out. -/
structure MachineCodec (spec : OracleSpec ι) (α : Type) where
  /-- Decode a machine output as a move. -/
  decodeMove : List Bool → Move spec α
  /-- Encode one log entry (oracle, query, answer). -/
  encodeEntry : (Σ i, spec.dom i × spec.rng i) → List Bool
  /-- The output when the budget is exhausted. -/
  timeout : α

namespace MachineCodec

variable {spec : OracleSpec ι}

/-- The encoding of a query log handed to the machine: the nested pair of its entries' encodings,
`⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`. -/
def encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) : List Bool :=
  h.foldr (fun e acc => pairEncode (codec.encodeEntry e) acc) []

/-- The empty log is encoded as the empty string: `codec.encodeLog [] = []`. -/
theorem encodeLog_nil (codec : MachineCodec spec α) : codec.encodeLog [] = [] :=
  rfl

/-- A log is encoded entry by entry:
`codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h)`. -/
theorem encodeLog_cons (codec : MachineCodec spec α) (e : Σ i, spec.dom i × spec.rng i)
    (h : QueryLog spec) :
    codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h) :=
  rfl

end MachineCodec

/-- The computation of a next-move function `next` with query budget `q`, started from the log
`hist`: a final output stops; a query within budget asks the oracle and continues with the
answer appended to the log; a query when the budget is exhausted gives `timeout`. -/
def buildComp {spec : OracleSpec ι} (next : QueryLog spec → Move spec α) (timeout : α) :
    ℕ → QueryLog spec → OracleComp spec α
  | 0, hist => match next hist with
    | .ret a => .pure a
    | .query _ _ => .pure timeout
  | q + 1, hist => match next hist with
    | .ret a => .pure a
    | .query i x => .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))

section BuildComp

variable {spec : OracleSpec ι} {next : QueryLog spec → Move spec α} {timeout : α}
  {hist : QueryLog spec}

/-- With the budget spent, a final output stops the computation:
`buildComp next timeout 0 hist = pure a` when `next hist = ret a`. -/
theorem buildComp_zero_of_ret {a : α} (h : next hist = .ret a) :
    buildComp next timeout 0 hist = .pure a := by
  rw [buildComp, h]

/-- With the budget spent, a query gives the output `timeout` and asks nothing:
`buildComp next timeout 0 hist = pure timeout` when `next hist = query i x`. -/
theorem buildComp_zero_of_query {i : ι} {x : spec.dom i} (h : next hist = .query i x) :
    buildComp next timeout 0 hist = .pure timeout := by
  rw [buildComp, h]

/-- Within budget, a final output stops the computation:
`buildComp next timeout (q + 1) hist = pure a` when `next hist = ret a`. -/
theorem buildComp_succ_of_ret {q : ℕ} {a : α} (h : next hist = .ret a) :
    buildComp next timeout (q + 1) hist = .pure a := by
  rw [buildComp, h]

/-- Within budget, a query asks the oracle and continues with the entry appended to the log:
`buildComp next timeout (q + 1) hist =
query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))` when `next hist = query i x`.
-/
theorem buildComp_succ_of_query {q : ℕ} {i : ι} {x : spec.dom i} (h : next hist = .query i x) :
    buildComp next timeout (q + 1) hist =
      .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩])) := by
  rw [buildComp, h]

end BuildComp

/-- The computation built with budget `q` makes at most `q` queries, from every log. -/
theorem buildComp_costBoundedBy {spec : OracleSpec ι} (next : QueryLog spec → Move spec α)
    (timeout : α) : ∀ (q : ℕ) (hist : QueryLog spec),
      (buildComp next timeout q hist).CostBoundedBy (fun _ => 1) q
  | 0, hist => by
    cases h : next hist with
    | ret a => rw [buildComp_zero_of_ret h]; exact OracleComp.costBoundedBy_pure _ _ _
    | query i x => rw [buildComp_zero_of_query h]; exact OracleComp.costBoundedBy_pure _ _ _
  | q + 1, hist => by
    cases h : next hist with
    | ret a => rw [buildComp_succ_of_ret h]; exact OracleComp.costBoundedBy_pure _ _ _
    | query i x =>
      rw [buildComp_succ_of_query h]
      exact (OracleComp.costBoundedBy_query _ _ _ _ _).2
        ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩

/-- The oracle computation of the machine `D` at parameter `n`, with coins `r` and query budget
`q`: the machine's next-move function is one activation of `D` on the encoded log.
[PS10, Definition 96.1], generalized to oracle families and arbitrary outputs. -/
def _root_.Complexity.NUPPT.toComp {spec : OracleSpec ι} (D : NUPPT) (codec : MachineCodec spec α)
    (n q : ℕ) (r : D.Coins n) : OracleComp spec α :=
  buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []

/-- The computation of `D` is built from the empty log, the next move being `D`'s output on the
encoded log, decoded: `D.toComp codec n q r =
buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []`.
-/
theorem _root_.Complexity.NUPPT.toComp_eq {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
    D.toComp codec n q r =
      buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout
        q [] :=
  rfl

/-- A machine's computation makes at most `q` queries. -/
theorem _root_.Complexity.NUPPT.toComp_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
    (D.toComp codec n q r).CostBoundedBy (fun _ => 1) q :=
  buildComp_costBoundedBy _ _ q []

/-- The oracle computation of the machine `D` **on input `x`** (for example a public key or a
challenge) at parameter `n`, with coins `r` and query budget `q`: the next-move function is one
activation of `D` on `⟨x, encoded log⟩`. -/
def _root_.Complexity.NUPPT.toCompOn {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) : OracleComp spec α :=
  buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
    codec.timeout q []

/-- The computation of `D` on the input `x` is built from the empty log, the next move being
`D`'s output on `⟨x, encoded log⟩`, decoded: `D.toCompOn codec n q x r =
buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
codec.timeout q []`. -/
theorem _root_.Complexity.NUPPT.toCompOn_eq {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) :
    D.toCompOn codec n q x r =
      buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
        codec.timeout q [] :=
  rfl

/-- A machine's computation on an input makes at most `q` queries. -/
theorem _root_.Complexity.NUPPT.toCompOn_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) :
    (D.toCompOn codec n q x r).CostBoundedBy (fun _ => 1) q :=
  buildComp_costBoundedBy _ _ q []

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/OracleComp.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Notation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle computations

The syntax of security games and protocols. An *oracle specification* names a family of oracles,
each with a type of queries and a type of answers. An *oracle computation* over it asks one
oracle a query, looks at the answer, chooses what to do next, and eventually returns a value. It
is the free monad over the specification: a well-founded tree (every run makes finitely many
queries) whose inner nodes are queries, with one subtree per possible answer. With finite answer
types, as for probabilistic computations, the tree is finite.

Everything else in the framework is built on this file:
- uniform sampling is one more oracle (`TCSlib.Cryptography.Games.Probability`);
- running a computation against implementations of its oracles is `simulate`
  (`TCSlib.Cryptography.Games.Simulate`);
- a two-party protocol is a pair of computations whose oracle is the message exchange
  (`TCSlib.Cryptography.Games.Protocols`).

With one oracle, an oracle computation is a `TCSlib.Cryptography.QueryTree` of the concrete
layer ([Gar26]); the bridge between the two is in the S2b layer.

## Main definitions

* `Games.OracleSpec ι`: a family of oracles named by `ι`.
* `Games.OracleComp spec α`: computations with access to the oracles of `spec`, returning an `α`;
  a `Monad` and a `LawfulMonad`.
* `Games.OracleComp.call i x`: ask oracle `i` the query `x` and return the answer.
* `Games.singleSpec I O`: one oracle (index `Unit`); its computations are the concrete layer's
  query trees.
* `Games.OracleSpec.add`: the disjoint union of two oracle families;
  `OracleComp.liftLeft`/`liftRight` run a computation over one part in the union.
* `Games.OracleComp.AllOutputs P c`: every possible output of `c` satisfies `P`.
* `Games.OracleComp.CostBoundedBy cost c q`: every run of `c` spends at most `q`, oracle `i`
  costing `cost i` per query (for example, 1 for the oracle under attack and 0 for coin draws).

## Main results

* `Games.OracleComp.instLawfulMonad`: the monad laws.
* `Games.OracleComp.CostBoundedBy.bind`: costs add under sequencing.
* `Games.OracleComp.costBoundedBy_liftLeft`, `costBoundedBy_liftRight`: lifting into a union of
  specifications keeps the cost.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

/-- A **family of oracles** named by `ι`: oracle `i` accepts queries in `dom i` and answers in
`rng i`. [VCVio, OracleComp/OracleSpec] -/
structure OracleSpec (ι : Type) where
  /-- The queries oracle `i` accepts. -/
  dom : ι → Type
  /-- The answers oracle `i` gives. -/
  rng : ι → Type

/-- **Oracle computations** over `spec` returning an `α`: either return a value, or ask oracle
`i` the query `x` and continue with `k` applied to the answer. This is the free monad over
`spec`; an oracle adversary of [Gar26, Definition 3.9] or [PS10, §3.8.1] with fixed coins is the
one-oracle case. [VCVio, OracleComp/OracleComp] -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type where
  /-- Return `a` without further queries. -/
  | pure : α → OracleComp spec α
  /-- Ask oracle `i` the query `x`, and continue with `k` on the answer. -/
  | query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {α β γ : Type}

/-- Sequencing: run `c`, then `f` on its result. Queries of `c` come first. -/
def bind : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | .pure a, f => f a
  | .query i x k, f => .query i x (fun y => bind (k y) f)

instance : Monad (OracleComp spec) where
  pure := .pure
  bind := bind

/-- `>>=` is `OracleComp.bind`. -/
theorem bind_eq_bind (c : OracleComp spec α) (f : α → OracleComp spec β) :
    (c >>= f) = c.bind f := rfl

/-- `pure` is the constructor `OracleComp.pure`. -/
theorem pure_eq_pure (a : α) : (Pure.pure a : OracleComp spec α) = .pure a := rfl

/-- `<$>` is sequencing with a return. -/
theorem map_eq_bind (h : α → β) (c : OracleComp spec α) :
    (h <$> c) = c.bind (fun a => .pure (h a)) := rfl

/-- Returning first, then continuing, is continuing. -/
@[simp] theorem pure_bind (a : α) (f : α → OracleComp spec β) : (OracleComp.pure a).bind f = f a :=
  rfl

/-- A query followed by `f` is the query whose continuation is followed by `f`. -/
@[simp] theorem query_bind (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : α → OracleComp spec β) :
    (OracleComp.query i x k).bind f = .query i x (fun y => (k y).bind f) := rfl

/-- Continuing with a return changes nothing. -/
@[simp] theorem bind_pure (c : OracleComp spec α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- Sequencing is associative. -/
theorem bind_assoc (c : OracleComp spec α) (f : α → OracleComp spec β)
    (g : β → OracleComp spec γ) : (c.bind f).bind g = c.bind (fun a => (f a).bind g) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- The monad laws. -/
instance instLawfulMonad : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (id_map := fun c => bind_pure c)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun c f g => bind_assoc c f g)

/-- Ask oracle `i` the query `x` and return the answer. -/
def call (i : ι) (x : spec.dom i) : OracleComp spec (spec.rng i) :=
  .query i x .pure

/-- Asking and then continuing with `f` is the query with continuation `f`. -/
@[simp] theorem call_bind (i : ι) (x : spec.dom i) (f : spec.rng i → OracleComp spec α) :
    (call i x).bind f = .query i x f := rfl

/-! ### Unions of oracle families -/

end OracleComp

/-- A single oracle with queries in `I` and answers in `O` (index type `Unit`). The concrete
layer's query trees are the computations over it (`TCSlib.Cryptography.QueryTree`). -/
abbrev singleSpec (I O : Type) : OracleSpec Unit := ⟨fun _ => I, fun _ => O⟩

/-- The single oracle of `singleSpec I O` takes queries in `I`. -/
theorem singleSpec_dom (I O : Type) (u : Unit) : (singleSpec I O).dom u = I := rfl

/-- The single oracle of `singleSpec I O` answers in `O`. -/
theorem singleSpec_rng (I O : Type) (u : Unit) : (singleSpec I O).rng u = O := rfl

/-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
    OracleSpec (ι₁ ⊕ ι₂) :=
  ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {α β : Type}

/-- Run a computation over `s₁` inside the union `s₁.add s₂`, asking only oracles of `s₁`. -/
def liftLeft {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₁ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query i x k => .query (.inl i) x (fun y => liftLeft (k y))

/-- Run a computation over `s₂` inside the union `s₁.add s₂`, asking only oracles of `s₂`. -/
def liftRight {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₂ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query j x k => .query (.inr j) x (fun y => liftRight (k y))

/-- Lifting commutes with sequencing. -/
theorem liftLeft_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₁ α)
    (f : α → OracleComp s₁ β) :
    (liftLeft (s₂ := s₂) (c.bind f)) = (liftLeft c).bind (fun a => liftLeft (f a)) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, liftLeft, ih]

/-- Lifting commutes with sequencing. -/
theorem liftRight_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₂ α)
    (f : α → OracleComp s₂ β) :
    (liftRight (s₁ := s₁) (c.bind f)) = (liftRight c).bind (fun a => liftRight (f a)) := by
  induction c with
  | pure a => rfl
  | query j x k ih => simp only [query_bind, liftRight, ih]

/-! ### Query costs -/

variable {spec : OracleSpec ι₁}

/-- `c` is **cost-bounded by `q`**: along every run, the total cost of its queries, oracle `i`
costing `cost i` per query, is at most `q`. With `cost` equal to 1 on the oracle under attack and
0 elsewhere, this is "at most `q` queries to that oracle", the query bound of
[Gar26, Definition 3.9]. -/
def CostBoundedBy (cost : ι₁ → ℕ) : OracleComp spec α → ℕ → Prop
  | .pure _, _ => True
  | .query i _ k, q => cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i)

/-- A return costs nothing. -/
@[simp] theorem costBoundedBy_pure (cost : ι₁ → ℕ) (a : α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.pure (spec := spec) a) q :=
  trivial

/-- A query is within budget `q` exactly when its cost fits and every continuation fits in what
is left. -/
@[simp] theorem costBoundedBy_query (cost : ι₁ → ℕ) (i : ι₁) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.query i x k) q ↔
      cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i) :=
  Iff.rfl

/-- A larger budget is still a bound. -/
theorem CostBoundedBy.mono {cost : ι₁ → ℕ} {c : OracleComp spec α} {q q' : ℕ}
    (h : CostBoundedBy cost c q) (hq : q ≤ q') : CostBoundedBy cost c q' := by
  induction c generalizing q q' with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := h
    exact ⟨Nat.le_trans hi hq, fun y => ih y (hk y) (Nat.sub_le_sub_right hq _)⟩

/-- **Costs add under sequencing:** if `c` fits in `q₁` and every continuation `f a` fits in
`q₂`, then `c` followed by `f` fits in `q₁ + q₂`.

**Proof sketch.** Induction on `c`. At a query of cost `cost i ≤ q₁`, the continuation fits in
`q₁ - cost i` by hypothesis, so by induction it fits in `(q₁ - cost i) + q₂`, which is
`(q₁ + q₂) - cost i`. -/
theorem CostBoundedBy.bind {cost : ι₁ → ℕ} {c : OracleComp spec α} {f : α → OracleComp spec β}
    {q₁ q₂ : ℕ} (hc : CostBoundedBy cost c q₁) (hf : ∀ a, CostBoundedBy cost (f a) q₂) :
    CostBoundedBy cost (c.bind f) (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a => exact (hf a).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    refine ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y)

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
left part. -/
theorem costBoundedBy_liftLeft {s₂ : OracleSpec ι₂} {cost : ι₁ ⊕ ι₂ → ℕ} {c : OracleComp spec α}
    {q : ℕ} (h : CostBoundedBy (fun i => cost (.inl i)) c q) :
    CostBoundedBy cost (liftLeft (s₂ := s₂) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query i x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
right part. -/
theorem costBoundedBy_liftRight {s₁ : OracleSpec ι₂} {cost : ι₂ ⊕ ι₁ → ℕ}
    {c : OracleComp spec α} {q : ℕ} (h : CostBoundedBy (fun j => cost (.inr j)) c q) :
    CostBoundedBy cost (liftRight (s₁ := s₁) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query j x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-! ### Possible outputs -/

/-- **Every possible output** of `c` satisfies `P`: a return satisfies it, and every
continuation of a query does, whatever the answer. -/
def AllOutputs {spec : OracleSpec ι} (P : α → Prop) : OracleComp spec α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ y, AllOutputs P (k y)

/-- The only possible output of a return is its value: `(pure a).AllOutputs P ↔ P a`. -/
theorem allOutputs_pure {spec : OracleSpec ι} {P : α → Prop} {a : α} :
    (OracleComp.pure (spec := spec) a).AllOutputs P ↔ P a :=
  Iff.rfl

/-- The possible outputs of a query are those of its continuations, whatever the answer:
`(query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P`. -/
theorem allOutputs_query {spec : OracleSpec ι} {P : α → Prop} {i : ι} {x : spec.dom i}
    {k : spec.rng i → OracleComp spec α} :
    (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P :=
  Iff.rfl

/-- Every computation satisfies the trivial predicate at every possible output. -/
theorem allOutputs_true {spec : OracleSpec ι} (c : OracleComp spec α) :
    c.AllOutputs fun _ => True := by
  induction c with
  | pure a => trivial
  | query i x k ih => exact fun y => ih y

/-- `AllOutputs` is monotone in the predicate. -/
theorem AllOutputs.mono {spec : OracleSpec ι} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a)
    {c : OracleComp spec α} (h : c.AllOutputs P) : c.AllOutputs Q := by
  induction c with
  | pure a => exact hPQ a h
  | query i x k ih => exact fun y => ih y (h y)

/-- Every possible output of `c` followed by `f` satisfies `Q` when every possible output `a`
of `c` satisfies `P` and every possible output of `f a` with `P a` satisfies `Q`. -/
theorem AllOutputs.bind {spec : OracleSpec ι} {P : α → Prop} {Q : β → Prop}
    {c : OracleComp spec α} {f : α → OracleComp spec β} (hc : c.AllOutputs P)
    (hf : ∀ a, P a → (f a).AllOutputs Q) : (c.bind f).AllOutputs Q := by
  induction c with
  | pure a => exact hf a hc
  | query i x k ih => exact fun y => ih y (hc y)

end OracleComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Protocols.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party protocols as oracle computations

A party of a two-party protocol is an oracle computation with two kinds of oracles: the message
exchange (send a message, receive the other party's next message) and its own coins. Running the
protocol interleaves the two parties as coroutines: the active party runs until it sends a
message, the other party resumes with that message and runs until it replies, and so on, for at
most `fuel` messages.

**When a party returns.** [PS10, §4.4] ends the protocol when the active machine halts, and gives
a machine an output only on halting, so the waiting party has none. Yet Definitions 116.1 and
155.1 use both parties' outputs. Following the ch. 2–4 layer's foundation decision D8
(`TCSlib.Cryptography.ZeroKnowledge.Interaction`), both parties have outputs: the waiting party is
activated **once more**. Its pending send is answered `none` ("the other party has finished"), it
may draw coins, and it must then return without sending. A send after the end is reported
(`ExecOutcome.sentAfterEnd`), never hidden.

**A broader model than D8's.** The executor is a coroutine model that contains D8's. It is broader
in two respects. A party may return early (D8 fixes the number of messages). And a party's output
is a separate return value (in D8 it is the next-message function on the complete history, so the
last sender's output equals its last message). D8's executions are those of *embedded strategies*:
each samples its whole tape first, sends `next` on its scheduled turns, and returns `next` on its
complete history. Agreement with D8 is claimed only for that class (bridge B4, S2b).

**Traces.** `Party.execT` returns, beside the outcome, each party's received messages (the second
mover's first message first) and the coin draws it executed (`Party.Obs`). Its outcome is that of
`Party.exec` (`Party.execT_outcome`). A [PS10, §4.4] view `(x, z, r, M)` contains the whole random
tape `r`, including bits never read. It is recovered from the trace only for parties that sample
their whole tape first, as an embedded strategy does. Inputs and auxiliary inputs are Lean
parameters of the party. A party's own oracle log would miss the second mover's first message,
which reaches it as an argument.

The ch. 2–4 layer's strategies (`TCSlib.Cryptography.Strategy`, `TCSlib.Cryptography.exec`) remain
the definitions of interaction for IP, ZK and two-party computation (ruling of 2026-11-05). This
executor is the calculus in which their properties are proved, through B4.

## Main definitions

* `Games.exchangeSpec Out In`: the message-exchange oracle (send an `Out`, receive an `In` or
  `none`).
* `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
  an `α`.
* `Games.ExecOutcome`: both outputs, out of fuel, or a send after the end.
* `Games.Party.step`, `Games.Party.close`: run a party to its next send or return; close a party
  whose counterpart has returned.
* `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
  messages.
* `Games.Party.Obs`, `Games.Party.execT`: the traced execution, recording each party's received
  messages and coins.

## Main results

* `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.
* `Games.Party.execT_outcome`: the traced execution has the outcome of the execution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views), Definitions 116.1 and 155.1.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

/-- The **message-exchange oracle**: the query is the message sent, and the answer is the other
party's next message, or `none` if the other party has returned. [PS10, §4.4] -/
abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _ => Option In⟩

/-- A **party** of a two-party protocol: sends messages of type `Out`, receives messages of type
`In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α

/-- The **outcome of an execution**: both outputs; the message budget ran out; or a party sent a
message after its counterpart had returned. -/
inductive ExecOutcome (α β : Type) : Type where
  /-- Both parties returned: the first mover's output and the second mover's. -/
  | done (a : α) (b : β)
  /-- The message budget ran out before both parties returned. -/
  | outOfFuel
  /-- A party sent a message after its counterpart had returned. -/
  | sentAfterEnd

/-- Exchange the roles in an outcome. -/
def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
  | .done a b => .done b a
  | .outOfFuel => .outOfFuel
  | .sentAfterEnd => .sentAfterEnd

/-- Exchanging the roles exchanges the outputs: `(done a b).swap = done b a`. -/
theorem ExecOutcome.swap_done {α β : Type} (a : α) (b : β) :
    (ExecOutcome.done a b).swap = .done b a :=
  rfl

/-- A spent budget stays a spent budget: `outOfFuel.swap = outOfFuel`. -/
theorem ExecOutcome.swap_outOfFuel {α β : Type} :
    (ExecOutcome.outOfFuel : ExecOutcome α β).swap = .outOfFuel :=
  rfl

/-- A send after the end stays one: `sentAfterEnd.swap = sentAfterEnd`. -/
theorem ExecOutcome.swap_sentAfterEnd {α β : Type} :
    (ExecOutcome.sentAfterEnd : ExecOutcome α β).swap = .sentAfterEnd :=
  rfl

namespace Party

variable {Out In α β : Type}

/-- Run a party until it returns or sends a message, passing its coin draws through. The result is
either its output, or the message it sends together with how it continues on the reply. -/
def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out In α)))
  | .pure a => .pure (.inl a)
  | .query (.inl ()) m k => .pure (.inr (m, k))
  | .query (.inr j) x k => .query j x (fun y => step (k y))

/-- A returned party is done: `step (pure a) = pure (inl a)`. -/
theorem step_pure (a : α) : step (OracleComp.pure a : Party Out In α) = .pure (.inl a) :=
  rfl

/-- A party sending `m` stops there, with `m` and its continuation on the reply:
`step (query (inl ()) m k) = pure (inr (m, k))`. -/
theorem step_send (m : Out) (k : Option In → Party Out In α) :
    step (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inl ()) m k) =
      .pure (.inr (m, k)) :=
  rfl

/-- A coin draw of a party is passed through:
`step (query (inr j) x k) = query j x (fun y => step (k y))`. -/
theorem step_coin (j : ℕ) (x : Unit) (k : Fin (j + 1) → Party Out In α) :
    step (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inr j) x k) =
      .query j x (fun y => step (k y)) :=
  rfl

/-- **Close** a party whose counterpart has returned (its pending send already answered `none`):
it may still draw coins, and returns `some` of its output, or `none` if it sends a message. -/
def close : Party Out In α → ProbComp (Option α)
  | .pure a => .pure (some a)
  | .query (.inl ()) _ _ => .pure none
  | .query (.inr j) x k => .query j x (fun y => close (k y))

/-- Closing a returned party gives its output: `close (pure a) = pure (some a)`. -/
theorem close_pure (a : α) : close (OracleComp.pure a : Party Out In α) = .pure (some a) :=
  rfl

/-- Closing a party that sends gives `none`: `close (query (inl ()) m k) = pure none`. -/
theorem close_send (m : Out) (k : Option In → Party Out In α) :
    close (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inl ()) m k) =
      .pure none :=
  rfl

/-- Closing passes a coin draw through:
`close (query (inr j) x k) = query j x (fun y => close (k y))`. -/
theorem close_coin (j : ℕ) (x : Unit) (k : Fin (j + 1) → Party Out In α) :
    close (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inr j) x k) =
      .query j x (fun y => close (k y)) :=
  rfl

/-- The end of an execution in which the active party returned `a`: the waiting party `B` is
activated once more, with `none`, and closed. -/
def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β) :=
  (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a))

/-- The end of an execution closes the waiting party on `none`, and reports `done a b` if it
returns `b` and `sentAfterEnd` if it sends:
`endWith a B = (close (B none)).bind fun ob => pure (ob.elim sentAfterEnd (done a))`. -/
theorem endWith_eq {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    endWith a B =
      (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a)) :=
  rfl

/-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
waits for `A`'s first message. After each message the roles swap. A return costs no fuel; when the
active party returns, the waiting party is activated once more and closed (`endWith`).

**Deviation from [PS10, §4.4]:** the source ends the protocol when the active machine halts and
defines outputs only on halting, so the waiting party would have none, while Definitions 116.1
and 155.1 use both outputs. Following the ch. 2–4 layer's D8, the waiting party is activated once
more; it may draw coins, but a send is reported as `sentAfterEnd`.

**Relation to D8.** This executor is broader than D8 in two respects. A party may return early
(D8 fixes the number of messages). And a party's output is a separate return value, computed after
its last activation and possibly after fresh coins on closure. In D8 a party's output is its
next-message function on its complete history, so the last sender's output equals its last
message (`Protocol.outV_eq_getLast_of_moverIsV`). D8's executions are the executions of embedded
strategies (each samples its whole tape first, sends `next` on its scheduled turns, and returns
`next` on its complete history). Agreement with D8 is claimed only for that class (bridge B4). -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (ExecOutcome α β)
  | 0, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel))
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B)
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap))

/-- With no fuel, the first mover runs until it returns or tries to send. If it returns, the
waiting party is closed (`endWith`): activated with `none`, it may draw coins, and the outcome is
`done` if it returns and `sentAfterEnd` if it sends. If the first mover tries to send, the outcome
is `outOfFuel` and the waiting party never runs. -/
@[simp] theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
    exec 0 A B = (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel)) :=
  rfl

/-- One message of the execution: `A` runs until it returns (then `B` is closed) or sends `m`
(then `B` resumes with `m` as the first mover, against `A`'s continuation). -/
theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β) :
    exec (fuel + 1) A B =
      (step A).bind (Sum.elim (fun a => endWith a B)
        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap)) :=
  rfl

/-! ### Sanity checks: fuel counts messages; a send after the end is reported -/

example (a b : Bool) :
    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := rfl

example (m : Unit) (a b : Bool) :
    exec 1 (M₂ := Unit) (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) =
      .pure (.done a b) := rfl

example (m : Unit) (a b : Bool) :
    exec 1 (M₁ := Unit) (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) =
      .pure .sentAfterEnd := rfl

/-! ### The traced execution -/

/-- What one party **observes** during an execution: the messages delivered to it, in order, and
the coins it drew, each as a sampling oracle `m` with its answer in `Fin (m + 1)`. -/
structure Obs (In : Type) : Type where
  /-- The messages delivered to the party, in order. -/
  received : List In
  /-- The party's coin draws, in order. -/
  coins : List (Σ m : ℕ, Fin (m + 1))

/-- `step`, also returning the coins drawn along the way. -/
def stepT : Party Out In α →
    ProbComp ((α ⊕ (Out × (Option In → Party Out In α))) × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (.inl a, [])
  | .query (.inl ()) m k => .pure (.inr (m, k), [])
  | .query (.inr j) x k => .query j x fun y =>
      (stepT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- `close`, also returning the coins drawn along the way. -/
def closeT : Party Out In α → ProbComp (Option α × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (some a, [])
  | .query (.inl ()) _ _ => .pure (none, [])
  | .query (.inr j) x k => .query j x fun y =>
      (closeT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- The traced end of an execution: `endWith`, also returning the waiting party's coins. -/
def endWithT {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β × List (Σ m : ℕ, Fin (m + 1))) :=
  (closeT (B none)).bind fun p => .pure (Option.elim p.1 .sentAfterEnd (ExecOutcome.done a), p.2)

/-- The **traced execution**: `exec`, also returning what each party observed. The first component
of the result is the outcome, the second the first mover's observations, and the third the second
mover's. When the active party sends `m`, `m` is the first message the other party receives in the
rest of the run. [PS10, §4.4] (the received messages of a view; its random tape for parties that
sample it first) -/
def execT : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) →
      ProbComp (ExecOutcome α β × Obs M₂ × Obs M₁)
  | 0, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun _ => .pure (.outOfFuel, ⟨[], p.2⟩, ⟨[], []⟩)) p.1
  | fuel + 1, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun mk => (execT fuel (B (some mk.1)) mk.2).bind fun r =>
        .pure (r.1.swap, ⟨r.2.2.received, p.2 ++ r.2.2.coins⟩,
          ⟨mk.1 :: r.2.1.received, r.2.1.coins⟩)) p.1

/-- An ended execution never reports a spent budget: the outcome of `endWithT` is `done` or
`sentAfterEnd`. -/
theorem endWithT_ne_outOfFuel {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).AllOutputs fun q => q.1 ≠ .outOfFuel := by
  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
  rcases p with ⟨_ | b, cs⟩ <;>
    simp only [OracleComp.allOutputs_pure, Option.elim_none, Option.elim_some, ne_eq,
      reduceCtorEq, not_false_eq_true]

/-- **Trace invariants** (gate 02 round 2, note 5): on every possible run of
`execT fuel A B`, write `M_A` and `M_B` for the messages delivered to the first and the second
mover. Then `|M_A| + |M_B| ≤ fuel`; the second mover has received as many messages as the first
or one more (it receives first); and a spent budget means exactly `fuel` messages were delivered.

**Proof sketch.** Induction on `fuel`, generalizing the parties and their types. A return or a
blocked send delivers nothing (both lists are empty), and `endWithT` never reports a spent budget.
A delivered message adds one message to the receiver, and the recursive run, with the roles
exchanged, satisfies the invariants with `fuel − 1`; exchanging back keeps them, since its first
mover is the original second mover. -/
theorem execT_trace : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).AllOutputs fun r =>
      r.2.1.received.length + r.2.2.received.length ≤ fuel ∧
      (r.2.2.received.length = r.2.1.received.length ∨
        r.2.2.received.length = r.2.1.received.length + 1) ∧
      (r.1 = .outOfFuel → r.2.1.received.length + r.2.2.received.length = fuel)
  | 0, _, _, _, _, A, B => by
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
    rcases p with ⟨a | mk, cs⟩
    · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
        OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun h => absurd h hq⟩
    · exact OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun _ => by simp⟩
  | fuel + 1, _, _, _, _, A, B => by
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
    rcases p with ⟨a | mk, cs⟩
    · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
        OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun h => absurd h hq⟩
    · refine OracleComp.AllOutputs.bind (execT_trace fuel (B (some mk.1)) mk.2) fun r hr => ?_
      obtain ⟨h1, h2, h3⟩ := hr
      refine OracleComp.allOutputs_pure.2 ⟨?_, ?_, fun h => ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · have : r.1 = .outOfFuel := by
          cases hr1 : r.1 <;> simp_all [ExecOutcome.swap]
        have := h3 this
        simp only [List.length_cons]; omega

/-- `stepT` projects to `step`. -/
theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) = step A := by
  induction A with
  | pure a => rfl
  | query i x k ih =>
    cases i with
    | inl u => cases u; rfl
    | inr j =>
      simp only [stepT, step, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `closeT` projects to `close`. -/
theorem closeT_fst (A : Party Out In α) : (closeT A).bind (fun p => .pure p.1) = close A := by
  induction A with
  | pure a => rfl
  | query i x k ih =>
    cases i with
    | inl u => cases u; rfl
    | inr j =>
      simp only [closeT, close, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `endWithT` projects to `endWith`. -/
theorem endWithT_fst {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).bind (fun q => .pure q.1) = endWith a B := by
  simp only [endWithT, endWith, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [← closeT_fst (B none), OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- **The traced execution has the execution's outcome.**

**Proof sketch.** Induction on the fuel, generalizing the parties and their types. Each level of
`execT` runs `stepT`, which projects to `step` (`stepT_fst`); the branch on the first component
then matches `exec`'s, with `endWithT` projecting to `endWith` and the recursive call to the
recursive call. -/
theorem execT_outcome : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).bind (fun r => .pure r.1) = exec fuel A B
  | 0, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | _, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · rfl
  | fuel + 1, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | mk, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · simp only [Sum.elim_inr, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← execT_outcome fuel (B (some mk.1)) mk.2, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]

end Party

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Simulate.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implementing oracles: simulation and logging

An oracle computation only *asks* its oracles. A security game decides how they answer: with a
keyed function, with fresh coins on every query (a randomized encryption oracle), refusing some
queries (a CCA2 decryption oracle that will not decrypt the challenge), or by asking other
oracles (a reduction that answers its adversary's queries with queries of its own). All of these
are *implementations*: for each oracle and query, a computation over a target specification that
returns the answer and updates a state. `simulate` runs a computation with every query answered
by an implementation, threading the state.

Logging is an implementation transformer: it answers as before and also appends every query and
its answer to a log kept in the state. Win conditions such as "the forged message was never
queried" are predicates on that log. Logging never changes the computation
(`simulate_withLog`).

## Main definitions

* `Games.QueryImpl spec σ spec'`: implementations of the oracles of `spec` by computations over
  `spec'`, with state `σ`.
* `Games.simulate impl c s`: run `c` from state `s`, answering its queries with `impl`.
* `Games.QueryImpl.ofComp`, `QueryImpl.passthrough`, `QueryImpl.sum`: stateless implementations,
  forwarding queries unchanged, and implementing two oracle families side by side.
* `Games.QueryLog spec`, `Games.QueryImpl.withLog`: the record of a run's queries and answers, and
  the logging transformer.
* `Games.QueryImpl.comp`: answering one implementation's queries with another.

## Main results

* `Games.simulate_bind`: simulation commutes with sequencing.
* `Games.simulate_withLog`: forgetting the log of a logged simulation gives the plain simulation.
* `Games.simulate_comp`: simulation composes; a reduction run against an implementation of its
  oracles is a single implementation of its adversary's oracles.
* `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
  of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
  simulation is cost-bounded by `q`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
-/

namespace TCSlib.Cryptography.Games

variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}

/-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
[VCVio, SimSemantics] -/
def QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

/-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
    OracleComp spec α → σ → OracleComp spec' (α × σ)
  | .pure a, s => .pure (a, s)
  | .query i x k, s => (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2)

section Simulate

variable {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec')

/-- Simulating a return returns it with the state unchanged. -/
@[simp] theorem simulate_pure (a : α) (s : σ) :
    simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl

/-- Simulating a query runs the implementation, then simulates the continuation. -/
@[simp] theorem simulate_query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (s : σ) :
    simulate impl (OracleComp.query i x k) s =
      (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2) := rfl

/-- **Simulation commutes with sequencing:** simulating `c` followed by `f` is simulating `c`,
then simulating `f` on its result from the state it reached.

**Proof sketch.** Induction on `c`; at a query, both sides run the implementation first, and the
monad's associativity lines up the continuations. -/
theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
  induction c generalizing s with
  | pure a => rfl
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  simp only [OracleComp.call, simulate_query, simulate_pure]
  exact OracleComp.bind_pure _

end Simulate

namespace QueryImpl

/-- A **stateless** implementation: oracle `i` answers query `x` by running `f i x`. -/
def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
  fun i x s => (f i x).bind (fun y => .pure (y, s))

/-- A stateless implementation runs `f i x` and keeps the state:
`ofComp f i x s = (f i x).bind (fun y => .pure (y, s))`. -/
theorem ofComp_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) (i : ι) (x : spec.dom i) (s : σ) :
    ofComp f i x s = (f i x).bind (fun y => .pure (y, s)) :=
  rfl

/-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
  ofComp (fun i x => OracleComp.call i x)

/-- Forwarding asks the same oracle the same query and keeps the state:
`passthrough i x s = .query i x (fun y => .pure (y, s))`. -/
theorem passthrough_apply {spec : OracleSpec ι} (i : ι) (x : spec.dom i) (s : σ) :
    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) :=
  rfl

/-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
`impl₁`, and `.inr j` by `impl₂`. -/
def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') :
    QueryImpl (s₁.add s₂) σ spec'
  | .inl i => impl₁ i
  | .inr j => impl₂ j

/-- Side by side, the oracle `.inl i` is answered by `impl₁`: `sum impl₁ impl₂ (.inl i) x s =
impl₁ i x s`. -/
theorem sum_inl {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (i : ι₁) (x : s₁.dom i)
    (s : σ) : sum impl₁ impl₂ (.inl i) x s = impl₁ i x s :=
  rfl

/-- Side by side, the oracle `.inr j` is answered by `impl₂`: `sum impl₁ impl₂ (.inr j) x s =
impl₂ j x s`. -/
theorem sum_inr {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (j : ι₂) (x : s₂.dom j)
    (s : σ) : sum impl₁ impl₂ (.inr j) x s = impl₂ j x s :=
  rfl

end QueryImpl

/-! ### Composing implementations -/

/-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
answers its adversary's queries by querying its own oracles becomes, after its oracles are
implemented, a single implementation of the adversary's oracles.
[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)] -/
def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
  fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))

/-- The composed implementation simulates `impl₁`'s answer with `impl₂` and regroups the states:
`impl₂.comp impl₁ i x s =
(simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))`. -/
theorem QueryImpl.comp_apply {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (i : ι) (x : spec.dom i) (s : σ₁ × σ₂) :
    impl₂.comp impl₁ i x s =
      (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2))) :=
  rfl

/-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
with the composed implementation, up to regrouping the states.
[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]

**Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
continuations agree by induction after associativity. -/
theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (c : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    simulate impl₂ (simulate impl₁ c s₁) s₂ =
      (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
  induction c generalizing s₁ s₂ with
  | pure a => rfl
  | query i x k ih =>
    simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
      OracleComp.pure_bind]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-! ### Logging -/

/-- The **log** of a run: the list of its queries, each with the oracle asked, the query and the
answer, in order. [VCVio, QueryTracking/LoggingOracle] -/
abbrev QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  List (Σ i, spec.dom i × spec.rng i)

/-- **Logging:** answer as `impl` does, and append each query and its answer to the log kept
beside the state. [VCVio, QueryTracking/LoggingOracle] -/
def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
  fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))

/-- The logged implementation answers as `impl` and appends the entry to the log:
`impl.withLog i x s = (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))`.
-/
theorem QueryImpl.withLog_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (i : ι) (x : spec.dom i) (s : σ × QueryLog spec) :
    impl.withLog i x s =
      (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩]))) :=
  rfl

/-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
simulation, whatever the initial log.

**Proof sketch.** Induction on the computation: at a query, the logged implementation is the
plain one followed by a return that only extends the log, and the continuations agree by
induction. -/
theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (c : OracleComp spec α) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate impl c s := by
  induction c generalizing s log with
  | pure a => rfl
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext ys
    exact ih ys.1 ys.2 _

/-! ### Costs under simulation -/

/-- **Costs under simulation:** if every call to oracle `i` is answered by a computation of cost
at most `b i` (target costs `cost'`), and `c` is cost-bounded by `q` when oracle `i` costs
`b i`, then the simulation of `c` is cost-bounded by `q`. With `b i = 1` for every oracle the
reduction asks once per query, the reduction makes no more target queries than its adversary
makes queries.

**Proof sketch.** Induction on `c`. At a query to oracle `i` with budget `q ≥ b i`, the
implementation fits in `b i`, and the simulated continuation fits in `q - b i` by induction, so
the sequence fits in `b i + (q - b i) = q` (`CostBoundedBy.bind`). -/
theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec σ spec'} {cost' : ι' → ℕ} {b : ι → ℕ}
    (himpl : ∀ i x s, OracleComp.CostBoundedBy cost' (impl i x s) (b i))
    {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
    OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
  induction c generalizing q s with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rwa [Nat.add_sub_cancel' hi] at h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed function families, random functions and the PRF advantage

At one fixed value of the security parameter, a function ensemble [Gar26, Definition 3.6]
is a random variable ranging over functions `I → O`. Following the concrete-layer
convention, random variables are pushforwards of uniform seeds, so an efficiently
computable ensemble [Gar26, Definition 3.8] is a *keyed family* `F : K → I → O`, sampled
by drawing a uniform key `k : K` and outputting `F k`. The random function ensemble
[Gar26, Definition 3.7] is the uniform distribution on the finite type `I → O`, sampled
by the identity.

The PRF advantage of an oracle adversary `A` [Gar26, Definition 3.9] is
`|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|`. It is the distinguishing advantage
`distAdv` of the oracle adversary viewed as a distinguisher of whole functions; the
adversary only ever sees the values at its queries, which is what makes the advantage
meaningful for bounded-query adversaries.

The efficiency conditions of Definition 3.8 (a polynomial-time key generator and
evaluator) and the quantification over non-uniform PPT adversaries of Definition 3.9
belong to the asymptotic layer; here the only resource tracked is the query bound
`OracleAdversary.BoundedBy`.

## Main definitions

* `randomFunction I O`: the sampler of a uniform random function `I → O`.
* `prfAdv F A`: the PRF advantage of the oracle adversary `A` against the keyed family `F`.

## Main results

* `prfAdv_eq`: the advantage written out as a difference of two probabilities.
* `prfAdv_nonneg`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.1, Definitions 3.6–3.9.
-/

namespace TCSlib.Cryptography

variable {K ρ σ σ' γ : Type*} {I O : Type}

/-- The sampler of a uniformly random function `I → O`: the seed is the function table
itself, a uniform element of the finite type `I → O`. This is the random function
ensemble `R_n` of [Gar26, Definition 3.7] at one value of the security parameter; its
seed has `|I| · log |O|` bits, `n · 2^n` for `I = O = {0,1}^n`. -/
def randomFunction (I O : Type*) : (I → O) → I → O := id

/-- The PRF advantage of the oracle adversary `A` against the keyed function family
`F : K → I → O` (a function ensemble [Gar26, Definitions 3.6 and 3.8], keys uniform in
`K`): `|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|` with `R` a uniform random
function, [Gar26, Definition 3.9] at one value of the security parameter. `F` is
pseudorandom when this is negligible for every efficient adversary; the concrete layer
bounds it by explicit reductions instead. -/
noncomputable def prfAdv [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : ℝ :=
  distAdv F (randomFunction I O) (oracleDist A)

/-- The PRF advantage written out: the difference between the probability that `A`
accepts with oracle `F k` for uniform `k` and coins `r`, and the probability that it
accepts with a uniform random function `R` as oracle. [Gar26, Definition 3.9]. -/
theorem prfAdv_eq [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A = |uprob (fun z : K × ρ => (A z.2).eval (F z.1) = true) -
      uprob (fun z : (I → O) × ρ => (A z.2).eval z.1 = true)| := rfl

/-- The PRF advantage is nonnegative. -/
theorem prfAdv_nonneg [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : 0 ≤ prfAdv F A :=
  abs_nonneg _

/-- Two samplers producing the same sample from every seed have the same acceptance
probability. -/
theorem acceptProb_congr [Fintype σ] [Fintype ρ] {X Y : σ → γ} (h : ∀ s, X s = Y s)
    (D : γ → ρ → Bool) : acceptProb X D = acceptProb Y D := by
  rw [funext h]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Goldwasser–Micali pseudorandom function

From a length-doubling generator `G(y) = G₀(y) ‖ G₁(y)` the GGM construction
[Gar26, Construction 3.3] defines `F_K(x₁ … x_n) = G_{x_n}(⋯ G_{x₁}(K) ⋯)`: walk down a
binary tree of depth `n` from the root label `K`, taking the left or right half of `G` at
each level according to the input bits. Theorem 3.3 of [Gar26] states that `F` is a
pseudorandom function if `G` is a pseudorandom generator.

This file proves the concrete form: for every oracle adversary `A` making at most `q`
queries,

  `prfAdv F A ≤ ∑_{i < n} ∑_{j < q} distAdv G U (B_{i,j})`,

where `B_{i,j}` (`ggmDist`) is an explicit PRG distinguisher built from `A`, and `U` is
the uniform distribution on pairs of seeds. Hence some `B_{i*,j*}` has advantage at
least `prfAdv F A / (n q)`.

The proof follows [Gar26]. The hybrid `H_i` (`hybridOracle G i`) labels the nodes of
level `i` by a random function `R_i` of the `i`-bit prefix and continues with `G` below
level `i`; `H_0` is `F` and `H_n` is a random function. Between `H_i` and `H_{i+1}` the
oracle is a fixed post-processing (`ggmFrom` from level `i + 1`) of a table indexed by
`i`-bit prefixes, holding `G(R_i(p))` in `H_i` and a uniform pair in `H_{i+1}`; the
sub-hybrid argument of `SubHybrids.lean` applied to the adversary `levelAdv G i A`,
which simulates this post-processing, bounds the gap.

The generator is taken in the form `G : S → S × S` over an arbitrary finite seed type
`S`; `ggmBits` and `ggmBits_prfAdv_le` restate the result for bit strings, with
`G : {0,1}^n → {0,1}^{2n}` split into halves.

## Main definitions

* `ggmFrom G x i y`: apply `G_{x_{i+1}}, …, G_{x_n}` to the label `y` of a level-`i` node.
* `ggm G`: the GGM keyed family `F_K(x) = ggmFrom G x 0 K`.
* `hybridOracle G i`, `hybridProb G A i`: the hybrid `H_i`.
* `levelAdv G i A`: the adversary on level-`i` tables simulating `A`.
* `ggmDist G A q i j`: the PRG distinguisher `B_{i,j}`.
* `ggmBits`: the construction on bit strings.

## Main results

* `hybridProb_zero`, `hybridProb_top`: `H_0 = F` and `H_n = R`.
* `hybridProb_level`: `|H_i - H_{i+1}| ≤ ∑_j distAdv G U B_{i,j}`.
* `ggm_prfAdv_le`, `exists_ggm_dist`: [Gar26, Theorem 3.3], concrete form.
* `ggmBits_prfAdv_le`, `exists_ggmBits_dist`: the same for `G : {0,1}^n → {0,1}^{2n}`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, Construction 3.3 and Theorem 3.3.
-/

namespace TCSlib.Cryptography

open Function QueryTree

attribute [local irreducible] uprob acceptProb

variable {S : Type} {ρ : Type*} {n : ℕ}

/-- Select the half `G_b` of a generator output: the first component for `b = false`
(the bit `0`) and the second for `b = true`. [Gar26, Construction 3.3]. -/
def pairSel (b : Bool) (v : S × S) : S := if b then v.2 else v.1

/-- The label of the leaf `x` below a node of level `i` with label `y`:
`G_{x_n}(⋯ G_{x_{i+1}}(y) ⋯)`, where the bits are `x 0, …, x (n-1)` (0-indexed).
For `i ≥ n` it is `y`. This is the loop of [Gar26, footnote 4 of §3.4.2] started at
step `i + 1`. -/
def ggmFrom (G : S → S × S) (x : Fin n → Bool) (i : ℕ) (y : S) : S :=
  if h : i < n then ggmFrom G x (i + 1) (pairSel (x ⟨i, h⟩) (G y)) else y
termination_by n - i

/-- Below the last level, one step of the walk applies `G_{x_{i+1}}`. -/
theorem ggmFrom_of_lt (G : S → S × S) (x : Fin n → Bool) {i : ℕ} (h : i < n) (y : S) :
    ggmFrom G x i y = ggmFrom G x (i + 1) (pairSel (x ⟨i, h⟩) (G y)) := by
  rw [ggmFrom, dif_pos h]

/-- At or below the leaves the walk stops: the label is returned unchanged. -/
theorem ggmFrom_of_le (G : S → S × S) (x : Fin n → Bool) {i : ℕ} (h : n ≤ i) (y : S) :
    ggmFrom G x i y = y := by
  rw [ggmFrom, dif_neg (by omega)]

/-- The GGM keyed function family [Gar26, Construction 3.3]: on key `K` and input
`x = x₁ … x_n`, `F_K(x) = G_{x_n}(G_{x_{n-1}}(⋯ G_{x₁}(K) ⋯))`. -/
def ggm (G : S → S × S) : S → (Fin n → Bool) → S := fun K x => ggmFrom G x 0 K

/-- The first `i` bits of `x`, as an `i`-bit string (bits beyond `n` read as `false`;
only `i ≤ n` is used). -/
def prefixAt (x : Fin n → Bool) (i : ℕ) : Fin i → Bool :=
  fun k => if h : k.val < n then x ⟨k, h⟩ else false

/-- The oracle of the hybrid `H_i` [Gar26, proof of Theorem 3.3]: with `R` a function
from `i`-bit prefixes to labels (the random function `K_i`), the input `x` is answered by
`G_{x_n}(⋯ G_{x_{i+1}}(R(x₁ … x_i)) ⋯)`: levels `0, …, i` of the tree are random and the
levels below are pseudorandom. -/
def hybridOracle (G : S → S × S) (i : ℕ) : ((Fin i → Bool) → S) → (Fin n → Bool) → S :=
  fun R x => ggmFrom G x i (R (prefixAt x i))

/-- The probability that `A` accepts in the hybrid `H_i`, with `R` uniform and uniform
coins. [Gar26, proof of Theorem 3.3]. -/
noncomputable def hybridProb [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (i : ℕ) : ℝ :=
  acceptProb (hybridOracle (n := n) G i) (oracleDist A)

/-- The hybrid `H_0` is the GGM function with a uniform key. [Gar26, proof of
Theorem 3.3, "`H_0` … identical to a pseudorandom function"]. -/
theorem hybridProb_zero [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) :
    hybridProb G A 0 = acceptProb (ggm G) (oracleDist A) := by
  have h : (fun s => hybridOracle G 0 ((Equiv.funUnique (Fin 0 → Bool) S).symm s)) =
      ggm (n := n) G := rfl
  rw [hybridProb, ← h, acceptProb_comp_equiv]

/-- The hybrid `H_n` is a uniform random function. [Gar26, proof of Theorem 3.3,
"`H_n` … identical to … a random function"]. -/
theorem hybridProb_top [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) :
    hybridProb G A n = acceptProb (randomFunction (Fin n → Bool) S) (oracleDist A) := by
  have hp : ∀ x : Fin n → Bool, prefixAt x n = x := fun x => funext fun k => dif_pos k.isLt
  exact acceptProb_congr (fun R => funext fun x => by
    rw [hybridOracle, ggmFrom_of_le G x le_rfl, hp]; rfl) _

/-- The adversary on level-`i` tables that simulates `A`: a query `x` of `A` becomes the
query `x₁ … x_i` to a table of pairs of labels, and the answer pair `v` is turned into
`G_{x_n}(⋯ G_{x_{i+2}}(G_{x_{i+1}}-half of v) ⋯)`. It makes as many queries as `A`. -/
def levelAdv (G : S → S × S) (i : Fin n) (A : OracleAdversary ρ (Fin n → Bool) S) :
    OracleAdversary ρ (Fin i → Bool) (S × S) :=
  fun r => (A r).simulate (fun x => prefixAt x i)
    (fun x v => ggmFrom G x (i + 1) (pairSel (x i) v))

/-- The hybrid `H_i` is the simulated adversary against the table `G ∘ R` of pairs of
pseudorandom labels at level `i + 1`. -/
theorem hybridProb_eq_level_prg [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (i : Fin n) :
    hybridProb G A i =
      acceptProb (fun R : (Fin i → Bool) → S => G ∘ R) (oracleDist (levelAdv G i A)) := by
  rw [hybridProb, acceptProb, acceptProb]
  refine uprob_congr fun z => iff_of_eq ?_
  simp only [oracleDist, levelAdv, eval_simulate, comp_apply]
  congr 2
  funext x
  rw [hybridOracle, ggmFrom_of_lt G x i.isLt]

/-- The hybrid `H_{i+1}` is the simulated adversary against a uniform table of pairs of
labels at level `i + 1`: a random function on `(i+1)`-bit prefixes is the same as a
random function from `i`-bit prefixes to pairs.

**Proof sketch.** Reparametrize the random function `R_{i+1}` by the bijection that
splits an `(i+1)`-bit prefix into its first `i` bits and its last bit, `R_{i+1}(p b) =`
the `b`-half of `T(p)`; then the `(i+1)`-bit prefix of `x` splits as the `i`-bit prefix
and the bit `x_{i+1}`, which is exactly how the simulated adversary answers. -/
theorem hybridProb_eq_level_random [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (i : Fin n) :
    hybridProb G A ((i : ℕ) + 1) =
      acceptProb (randomFunction (Fin i → Bool) (S × S)) (oracleDist (levelAdv G i A)) := by
  let e : ((Fin i → Bool) → S × S) ≃ ((Fin ((i : ℕ) + 1) → Bool) → S) :=
    { toFun := fun T y => pairSel (y (Fin.last i)) (T (Fin.init y))
      invFun := fun R p => (R (Fin.snoc p false), R (Fin.snoc p true))
      left_inv := fun T => funext fun p => by simp [pairSel, Fin.init_snoc]
      right_inv := fun R => funext fun y => by
        change pairSel (y (Fin.last i))
          (R (Fin.snoc (Fin.init y) false), R (Fin.snoc (Fin.init y) true)) = R y
        conv_rhs => rw [← Fin.snoc_init_self y]
        cases y (Fin.last i) <;> rfl }
  have hlast : ∀ x : Fin n → Bool, prefixAt x ((i : ℕ) + 1) (Fin.last i) = x i :=
    fun x => dif_pos i.isLt
  have hinit : ∀ x : Fin n → Bool, Fin.init (prefixAt x ((i : ℕ) + 1)) = prefixAt x i :=
    fun x => rfl
  rw [hybridProb, ← acceptProb_comp_equiv e, acceptProb, acceptProb]
  refine uprob_congr fun z => iff_of_eq ?_
  simp only [oracleDist, levelAdv, eval_simulate, comp_apply, randomFunction, id, e,
    Equiv.coe_fn_mk]
  congr 2
  funext x
  rw [hybridOracle, hlast, hinit]

/-- The PRG distinguisher `B_{i,j}` of [Gar26, proof of Theorem 3.3]. On a challenge
`z = (z₀, z₁) ∈ S × S` it runs `A` once, answering the queries whose `i`-bit prefix is
the `j`-th distinct prefix (0-indexed, in order of first appearance) by
`G_{x_n}(⋯ G_{x_{i+2}}(z_{x_{i+1}}) ⋯)`, earlier prefixes as in `H_{i+1}` and later
prefixes as in `H_i`, and outputs what `A` outputs.

*Cost*, for `A` bounded by `q` queries (`OracleAdversary.BoundedBy`; the definition itself
runs any `A`). One run of `A`; per query at most `n` evaluations of `G`; `q` fresh seeds and
`q` fresh pairs of seeds as coins together with `A`'s coins, which is lazy sampling of
`R_i` and `R_{i+1}` [Gar26, footnote 9]: no exponential table is sampled; maintaining the
list of at most `q` distinct prefixes. The indices `i, j` are non-uniform advice
[Gar26, footnotes 7 and 8]. -/
noncomputable def ggmDist [Fintype S] [Nonempty S] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (q : ℕ) (i : Fin n) (j : Fin q) :
    S × S → ((Fin q → S) × (Fin q → S × S)) × ρ → Bool :=
  tableDist G (levelAdv G i A) q j

/-- One level of the hybrid argument: the gap between `H_i` and `H_{i+1}` is at most the
sum over `j < q` of the PRG advantages of `B_{i,j}`. [Gar26, proof of Theorem 3.3,
sub-hybrids `H_{i,j}`].

**Proof sketch.** Write both hybrids as the simulated adversary `levelAdv G i A` against
a table of pseudorandom, respectively uniform, pairs, and apply the sub-hybrid
argument; the simulated adversary makes at most `q` queries. -/
theorem hybridProb_level [Fintype S] [Nonempty S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) {q : ℕ} (hA : A.BoundedBy q) (i : Fin n) :
    |hybridProb G A i - hybridProb G A ((i : ℕ) + 1)| ≤
      ∑ j : Fin q, distAdv G (id : S × S → S × S) (ggmDist G A q i j) := by
  rw [hybridProb_eq_level_prg, hybridProb_eq_level_random]
  exact table_hybrid G (levelAdv G i A) (fun r => (hA r).simulate _ _)

/-- **GGM security** [Gar26, Theorem 3.3], concrete form: for every oracle adversary `A`
making at most `q` queries, the PRF advantage of `A` against the GGM family is at most
the sum, over levels `i < n` and distinct-prefix indices `j < q`, of the PRG
distinguishing advantages of the explicit distinguishers `B_{i,j}` between `G` of a
uniform seed and a uniform pair of seeds.

**Deviation.** The source argues by contradiction and picks `i*, j*` with a large
neighbouring gap; the sum form is the exact quantitative content, and
`exists_ggm_dist` recovers the choice of `i*, j*`. The sub-hybrids are indexed by
distinct prefixes rather than by queries (see `SubHybrids.lean`).

**Proof sketch.** `H_0` is `F` and `H_n` is a random function; telescope over the levels
and bound each level by `hybridProb_level`. -/
theorem ggm_prfAdv_le [Fintype S] [Nonempty S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) {q : ℕ} (hA : A.BoundedBy q) :
    prfAdv (ggm G) A ≤
      ∑ i : Fin n, ∑ j : Fin q, distAdv G (id : S × S → S × S) (ggmDist G A q i j) := by
  rw [prfAdv, distAdv, ← hybridProb_zero, ← hybridProb_top]
  refine (abs_sub_le_sum_hybrids (fun i => hybridProb G A i) n).trans ?_
  rw [Finset.sum_range (fun i => |hybridProb G A i - hybridProb G A (i + 1)|)]
  exact Finset.sum_le_sum fun i _ => hybridProb_level G A hA i

/-- [Gar26, Theorem 3.3], existential form: if `n ≥ 1` and `q ≥ 1`, some distinguisher
`B_{i*,j*}` breaks `G` with advantage at least `prfAdv F A / (n q)`. The indices `i*, j*`
are the non-uniform advice of [Gar26, footnotes 7 and 8].

**Proof sketch.** Otherwise every term of `ggm_prfAdv_le` is below `ε / (n q)` and the
`n q` terms sum to less than `ε`. -/
theorem exists_ggm_dist [Fintype S] [Nonempty S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) {q : ℕ} (hA : A.BoundedBy q) (hn : 0 < n)
    (hq : 0 < q) :
    ∃ (i : Fin n) (j : Fin q), prfAdv (ggm G) A / (n * q) ≤
      distAdv G (id : S × S → S × S) (ggmDist G A q i j) := by
  by_contra h
  push_neg at h
  have hsum := ggm_prfAdv_le G A hA
  have hlt : ∑ i : Fin n, ∑ j : Fin q, distAdv G (id : S × S → S × S) (ggmDist G A q i j) <
      ∑ _i : Fin n, ∑ _j : Fin q, prfAdv (ggm G) A / (n * q) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => h i j
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hval : ∑ _i : Fin n, ∑ _j : Fin q, prfAdv (ggm G) A / (n * q) = prfAdv (ggm G) A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith

/-! ### Bit strings -/

/-- Splitting a `2n`-bit string into its first and last `n` bits, `z = z₀ ‖ z₁`, as a
bijection. With `G` length-doubling, the components of `splitHalves (G y)` are the halves
`G₀(y)` and `G₁(y)` of [Gar26, Construction 3.3]. -/
def splitHalves : (Fin (2 * n) → Bool) ≃ (Fin n → Bool) × (Fin n → Bool) where
  toFun z := (fun k => z ⟨k, by omega⟩, fun k => z ⟨n + k, by omega⟩)
  invFun w k := if h : k.val < n then w.1 ⟨k, h⟩ else w.2 ⟨k - n, by omega⟩
  left_inv z := funext fun k => by
    by_cases h : k.val < n
    · simp [h]
    · simp only [h, dite_false]
      congr 1; ext; simp; omega
  right_inv w := by
    refine Prod.ext (funext fun k => by simp) (funext fun k => ?_)
    simp only
    rw [dif_neg (by simp)]
    exact congrArg w.2 (Fin.ext (by simp))

/-- The GGM construction on bit strings [Gar26, Construction 3.3]: from a length-doubling
`G : {0,1}^n → {0,1}^{2n}`, the keyed family `F_K(x) = G_{x_n}(⋯ G_{x₁}(K) ⋯)` on
`n`-bit keys, inputs and outputs, with `G₀, G₁` the first and last `n` bits of `G`. -/
def ggmBits (G : (Fin n → Bool) → Fin (2 * n) → Bool) :
    (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool :=
  ggm (splitHalves ∘ G)

/-- The PRG distinguisher `B_{i,j}` for a length-doubling `G` on bit strings: split the
`2n`-bit challenge into halves and run `ggmDist`. Same cost as `ggmDist`. -/
noncomputable def ggmBitsDist (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) (q : ℕ) (i : Fin n) (j : Fin q) :
    (Fin (2 * n) → Bool) →
      ((Fin q → Fin n → Bool) × (Fin q → (Fin n → Bool) × (Fin n → Bool))) × ρ → Bool :=
  fun z c => ggmDist (splitHalves ∘ G) A q i j (splitHalves z) c

/-- The advantage of `ggmBitsDist` against `G` with a uniform `2n`-bit string is the
advantage of `ggmDist` against the split generator with a uniform pair. -/
theorem distAdv_ggmBitsDist [Fintype ρ] (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) (q : ℕ) (i : Fin n) (j : Fin q) :
    distAdv G (id : (Fin (2 * n) → Bool) → _) (ggmBitsDist G A q i j) =
      distAdv (splitHalves ∘ G) id (ggmDist (splitHalves ∘ G) A q i j) := by
  have h : acceptProb (id : (Fin (2 * n) → Bool) → _) (ggmBitsDist G A q i j) =
      acceptProb (id : (Fin n → Bool) × (Fin n → Bool) → _)
        (ggmDist (splitHalves ∘ G) A q i j) := by
    refine Eq.trans ?_ (acceptProb_comp_equiv splitHalves id _)
    rw [acceptProb, acceptProb]; rfl
  have h' : acceptProb G (ggmBitsDist G A q i j) =
      acceptProb (splitHalves ∘ G) (ggmDist (splitHalves ∘ G) A q i j) := by
    rw [acceptProb, acceptProb]; rfl
  rw [distAdv, distAdv, h, h']

/-- **GGM security for bit strings** [Gar26, Theorem 3.3], concrete form: for a
length-doubling `G : {0,1}^n → {0,1}^{2n}` and every oracle adversary making at most `q`
queries, the PRF advantage against `ggmBits G` is at most the sum over `i < n`, `j < q` of
the PRG advantages of `ggmBitsDist G A q i j` (between `G(U_n)` and `U_{2n}`). -/
theorem ggmBits_prfAdv_le [Fintype ρ] (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) {q : ℕ} (hA : A.BoundedBy q) :
    prfAdv (ggmBits G) A ≤
      ∑ i : Fin n, ∑ j : Fin q, distAdv G id (ggmBitsDist G A q i j) := by
  simp only [distAdv_ggmBitsDist]
  exact ggm_prfAdv_le _ A hA

/-- [Gar26, Theorem 3.3] for bit strings, existential form: if `n, q ≥ 1`, some
`B_{i*,j*}` distinguishes `G(U_n)` from `U_{2n}` with advantage at least
`prfAdv F A / (n q)`. -/
theorem exists_ggmBits_dist [Fintype ρ] (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) {q : ℕ} (hA : A.BoundedBy q)
    (hn : 0 < n) (hq : 0 < q) :
    ∃ (i : Fin n) (j : Fin q),
      prfAdv (ggmBits G) A / (n * q) ≤ distAdv G id (ggmBitsDist G A q i j) := by
  simp only [distAdv_ggmBitsDist]
  have : Nonempty (Fin n → Bool) := ⟨fun _ => false⟩
  exact exists_ggm_dist _ A hA hn hq

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lazy sampling of a random oracle

A random function `R : I → O` has `|O|^|I|` values, far too many for an efficient
reduction to sample. An oracle algorithm making at most `q` queries only ever looks at
`q` of them, and the standard remedy [Gar26, footnote 9 of §3.4] is *lazy sampling*: keep
a list of the distinct queries seen so far, answer a repeated query consistently, and
answer the `k`-th new query with a fresh value `W k`. This file proves that lazy
sampling with `q` uniform values `W : Fin q → O` produces exactly the same output
distribution as a uniform random function.

The lazy run is stated for an arbitrary answer stream `a : ℕ → O` (the answer to the
`k`-th distinct query is `a k`), so that hybrids can mix fresh values with other
answers index by index.

## Main definitions

* `QueryTree.noteQuery L x`: the list of distinct queries after querying `x`.
* `QueryTree.evalLazy a t L`: run `t`, answering the `k`-th distinct query by `a k`.
* `extendStream W`: a finite list of values `W : Fin q → O` as an answer stream.

## Main results

* `QueryTree.evalLazy_congr`: a run making at most `m` more queries only reads the first
  `L.length + m` entries of the answer stream.
* `QueryTree.uprob_evalLazy`: lazy sampling with `q` uniform fresh values has the same
  output distribution as a uniform random function, for trees making at most `q`
  queries.
* Probability helpers: `uprob_congr`, `uprob_prod_comm`, `uprob_snd`,
  `uprob_sections_congr`, `uprob_update_absorb`, `uprob_update_split`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, footnote 9 (lazy sampling of random functions).
-/

namespace TCSlib.Cryptography

open Function

section Helpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Events that are equivalent pointwise have the same probability. -/
theorem uprob_congr {p p' : α → Prop} (h : ∀ a, p a ↔ p' a) : uprob p = uprob p' :=
  congrArg uprob (funext fun a => propext (h a))

/-- Swapping the two coordinates of a product does not change probabilities. -/
theorem uprob_prod_comm (p : α → β → Prop) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : β × α => p z.2 z.1) :=
  (uprob_comp_equiv (Equiv.prodComm β α) (fun z : α × β => p z.1 z.2)).symm

/-- An event depending only on the second coordinate has the same probability on the
product. -/
theorem uprob_snd [Nonempty α] (p : β → Prop) :
    uprob (fun z : α × β => p z.2) = uprob p := by
  rw [uprob_prod_comm (fun _ b => p b)]
  exact uprob_fst p

/-- Two events on products with the same first factor have the same probability when
every section has the same probability. -/
theorem uprob_sections_congr (p : α → β → Prop) (p' : α → γ → Prop)
    (h : ∀ a, uprob (p a) = uprob (p' a)) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : α × γ => p' z.1 z.2) := by
  rw [uprob_prod, uprob_prod]
  exact congrArg uexp (funext h)

variable [DecidableEq α]

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform: the overwritten entry is absorbed. -/
theorem uprob_update_absorb [Nonempty β] (i : α) (f : (α → β) → γ → Prop) :
    uprob (fun z : β × ((α → β) × γ) => f (update z.2.1 i z.1) z.2.2) =
      uprob (fun z : (α → β) × γ => f z.1 z.2) := by
  let e : β × ((α → β) × γ) ≃ ((α → β) × γ) × β :=
    { toFun := fun z => ((update z.2.1 i z.1, z.2.2), z.2.1 i)
      invFun := fun w => (w.1.1 i, (update w.1.1 i w.2, w.1.2))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1.1 w.1.2)).trans
    (uprob_fst (fun w : (α → β) × γ => f w.1 w.2))

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform (version without extra coordinates). -/
theorem uprob_update_absorb' [Nonempty β] (i : α) (f : (α → β) → Prop) :
    uprob (fun z : β × (α → β) => f (update z.2 i z.1)) = uprob f := by
  let e : β × (α → β) ≃ (α → β) × β :=
    { toFun := fun z => (update z.2 i z.1, z.2 i)
      invFun := fun w => (w.1 i, update w.1 i w.2)
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1)).trans (uprob_fst f)

/-- If an event on a uniform table `W` depends on the entry `W i` only through a
parameter `v` (it does not otherwise read position `i`), its probability is the average
over `v` of the probability with `v` fixed. -/
theorem uprob_update_split [Nonempty β] (i : α) (g : β → (α → β) → Prop)
    (hg : ∀ v W u, g v (update W i u) ↔ g v W) :
    uprob (fun W => g (W i) W) = uexp (fun v => uprob (fun W => g v W)) := by
  rw [← uprob_prod (fun z : β × (α → β) => g z.1 z.2),
    ← uprob_update_absorb' i (fun W => g (W i) W)]
  exact uprob_congr fun z => by simp [hg]

end Helpers

namespace QueryTree

variable {I O α : Type} [DecidableEq I]

/-- The list of distinct queries after the query `x`, given the list `L` of distinct
queries so far: `x` is appended if it is new. -/
def noteQuery (L : List I) (x : I) : List I := if x ∈ L then L else L ++ [x]

/-- A repeated query leaves the list of distinct queries unchanged. -/
theorem noteQuery_of_mem {L : List I} {x : I} (h : x ∈ L) : noteQuery L x = L := if_pos h

/-- A new query is appended to the list of distinct queries. -/
theorem noteQuery_of_not_mem {L : List I} {x : I} (h : x ∉ L) : noteQuery L x = L ++ [x] :=
  if_neg h

/-- The index of the current query in the updated list is below its length. -/
theorem idxOf_noteQuery_lt (L : List I) (x : I) :
    (noteQuery L x).idxOf x < (noteQuery L x).length := by
  rw [List.idxOf_lt_length_iff]
  unfold noteQuery; split_ifs with h <;> simp [h]

/-- Querying adds at most one entry to the list of distinct queries. -/
theorem length_noteQuery_le (L : List I) (x : I) :
    (noteQuery L x).length ≤ L.length + 1 := by
  unfold noteQuery; split_ifs <;> simp

/-- Run `t` against a lazily sampled oracle: with `L` the list of distinct queries so
far, the query `x` is answered by `a k`, where `k` is the position of `x` among the
distinct queries in order of first appearance. A repeated query gets the same answer as
before. [Gar26, §3.4.2, footnote 9]. -/
def evalLazy (a : ℕ → O) : QueryTree I O α → List I → α
  | ret y, _ => y
  | query x k, L =>
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x)

/-- A leaf returns its output whatever the answers. -/
@[simp] theorem evalLazy_ret (a : ℕ → O) (y : α) (L : List I) :
    evalLazy a (ret y) L = y := rfl

/-- A query is recorded and answered by the stream entry at its position. -/
theorem evalLazy_query (a : ℕ → O) (x : I) (k : O → QueryTree I O α) (L : List I) :
    evalLazy a (query x k) L =
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x) := rfl

/-- A run making at most `m` further queries, started with `L` distinct queries already
seen, only reads the answer stream below `L.length + m`. -/
theorem evalLazy_congr {a b : ℕ → O} {t : QueryTree I O α} {m : ℕ} (ht : t.BoundedBy m)
    (L : List I) (hab : ∀ k < L.length + m, a k = b k) :
    evalLazy a t L = evalLazy b t L := by
  induction t using QueryTree.induct generalizing m L with
  | ret y => rfl
  | query x k ih =>
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
      have h1 := idxOf_noteQuery_lt L x
      have h2 := length_noteQuery_le L x
      rw [evalLazy_query, evalLazy_query, hab _ (by omega)]
      exact ih _ (ht _) _ fun j hj => hab j (by omega)

/-- Post-processing every lazy answer by `g` is the same as running the tree whose
answers are post-processed by `g`. -/
theorem evalLazy_comp {O' : Type} (g : O' → O) (a : ℕ → O') (t : QueryTree I O α)
    (L : List I) :
    evalLazy (g ∘ a) t L = evalLazy a (t.simulate id (fun _ => g)) L := by
  induction t using QueryTree.induct generalizing L with
  | ret y => rfl
  | query x k ih => exact ih _ _

end QueryTree

/-- A finite list `W : Fin q → O` of values as an answer stream; entries beyond `q` are
an arbitrary fixed value and are never read by trees making at most `q` queries. -/
noncomputable def extendStream {O : Type*} [Nonempty O] {q : ℕ} (W : Fin q → O) : ℕ → O :=
  fun k => if h : k < q then W ⟨k, h⟩ else Classical.arbitrary O

namespace QueryTree

variable {I : Type*} {O : Type*} {α : Type*} [DecidableEq I]

/-- A constant event has the same probability on any two nonempty finite types. -/
private theorem uprob_const_eq {β γ : Type*} [Fintype β] [Fintype γ] [Nonempty β]
    [Nonempty γ] (P : Prop) : uprob (fun _ : β => P) = uprob (fun _ : γ => P) := by
  by_cases h : P
  · rw [uprob_congr (p' := fun _ : β => True) (fun _ => iff_true_intro h),
      uprob_congr (p' := fun _ : γ => True) (fun _ => iff_true_intro h), uprob_true,
      uprob_true]
  · rw [uprob_congr (p' := fun _ : β => False) (fun _ => iff_false_intro h),
      uprob_congr (p' := fun _ : γ => False) (fun _ => iff_false_intro h), uprob_false,
      uprob_false]

/-- Keep the first `ℓ` entries of `W₀` and take the remaining entries from `W`. -/
private def combine {q : ℕ} (ℓ : ℕ) (W₀ W : Fin q → O) : Fin q → O :=
  fun i => if i.val < ℓ then W₀ i else W i

/-- The table answering a recorded query `x ∈ L` from the stream `a` at the position of `x`
in `L`, and every other query from `R`. -/
private def mergeTable (L : List I) (a : ℕ → O) (R : I → O) : I → O :=
  fun x => if x ∈ L then a (L.idxOf x) else R x

section Streams

variable [Nonempty O] {q : ℕ}

/-- Overwriting entry `j` of a value list does not change the stream at other positions. -/
theorem extendStream_update_of_ne (W : Fin q → O) (j : Fin q) (v : O) {k : ℕ}
    (hk : k ≠ j.val) : extendStream (update W j v) k = extendStream W k := by
  unfold extendStream
  split_ifs with h
  · exact update_of_ne (fun e => hk (by rw [← e])) _ _
  · rfl

/-- Overwriting entry `j` of a value list by `v` makes the stream read `v` at `j`. -/
theorem extendStream_update_self (W : Fin q → O) (j : Fin q) (v : O) :
    extendStream (update W j v) j.val = v := by
  simp [extendStream]

private theorem extendStream_combine_of_lt (W₀ W : Fin q → O) {ℓ k : ℕ} (hk : k < ℓ) :
    extendStream (combine ℓ W₀ W) k = extendStream W₀ k := by
  unfold extendStream combine
  split_ifs <;> simp_all

private theorem extendStream_combine_self (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    extendStream (combine ℓ W₀ W) ℓ = W ⟨ℓ, hℓ⟩ := by
  simp [extendStream, combine, hℓ]

omit [Nonempty O] in
private theorem combine_succ (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    combine ℓ W₀ W = combine (ℓ + 1) (update W₀ ⟨ℓ, hℓ⟩ (W ⟨ℓ, hℓ⟩)) W := by
  funext i
  unfold combine
  by_cases h1 : i.val < ℓ
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
    simp [h1, Nat.lt_succ_of_lt h1, this]
  · by_cases h2 : i.val = ℓ
    · have : i = ⟨ℓ, hℓ⟩ := Fin.ext h2
      subst this; simp
    · have : ¬ i.val < ℓ + 1 := by omega
      simp [h1, this]

omit [Nonempty O] in
private theorem combine_update (W₁ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) (u : O) :
    combine (ℓ + 1) W₁ (update W ⟨ℓ, hℓ⟩ u) = combine (ℓ + 1) W₁ W := by
  funext i
  unfold combine
  by_cases h : i.val < ℓ + 1
  · simp [h]
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h; exact h (Nat.lt_succ_self _)
    simp [h, this]

private theorem mergeTable_append (W₀ : Fin q → O) (R : I → O) {L : List I} {x : I}
    (hx : x ∉ L) (hℓ : L.length < q) :
    mergeTable L (extendStream W₀) R =
      mergeTable (L ++ [x]) (extendStream (update W₀ ⟨L.length, hℓ⟩ (R x))) R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · have hlt := List.idxOf_lt_length_of_mem hy
    rw [if_pos hy, if_pos (List.mem_append_left _ hy), List.idxOf_append_of_mem hy,
      extendStream_update_of_ne _ _ _ (by simp; omega)]
  · by_cases hyx : y = x
    · subst hyx
      rw [if_neg hy, if_pos (by simp), List.idxOf_append_of_notMem hy]
      simpa using (extendStream_update_self W₀ ⟨L.length, hℓ⟩ (R y)).symm
    · rw [if_neg hy, if_neg (by simp [hy, hyx])]

omit [Nonempty O] in
private theorem mergeTable_update (L : List I) (a : ℕ → O) (R : I → O) {x : I} (hx : x ∈ L)
    (u : O) : mergeTable L a (update R x u) = mergeTable L a R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · simp [hy]
  · have : y ≠ x := fun e => hy (e ▸ hx)
    simp [hy, this]

end Streams

end QueryTree

namespace QueryTree

variable {I O α : Type} [DecidableEq I]

/-- The generalized lazy-sampling invariant: started with `L` already recorded, with
answers `W₀` on `L`, the lazy run with fresh values beyond `L` and the run against a
random function agreeing with `W₀` on `L` have the same output distribution.

**Proof sketch.** Induction on the tree. A repeated query is answered by the recorded
value on both sides. For a new query `x`, the lazy side answers with the fresh entry at
position `|L|` and the table side with `R x`; record this answer `v` in `W₀`. Neither
continuation reads the entry again, so both probabilities are averages over `v` of the
continuation probabilities (`uprob_update_split`), which agree by induction. -/
private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {q : ℕ} (t : QueryTree I O α) : ∀ (m : ℕ) (L : List I) (W₀ : Fin q → O),
    t.BoundedBy m → L.length + m ≤ q →
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream (combine L.length W₀ W)) t L)) =
      uprob (fun R : I → O => φ (t.eval (mergeTable L (extendStream W₀) R))) := by
  induction t using QueryTree.induct with
  | ret y => intro _ _ _ _ _; exact uprob_const_eq (β := Fin q → O) (γ := I → O) (φ y)
  | query x k ih =>
    intro m L W₀ ht hm
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
    by_cases hx : x ∈ L
    · -- a repeated query: both sides answer with the recorded value
      have hi : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
      have hl : ∀ W, evalLazy (extendStream (combine L.length W₀ W)) (query x k) L =
          evalLazy (extendStream (combine L.length W₀ W)) (k (extendStream W₀ (L.idxOf x)))
            L := by
        intro W
        rw [evalLazy_query, noteQuery_of_mem hx, extendStream_combine_of_lt _ _ hi]
      have hr : ∀ R, (query x k).eval (mergeTable L (extendStream W₀) R) =
          (k (extendStream W₀ (L.idxOf x))).eval (mergeTable L (extendStream W₀) R) := by
        intro R; simp [mergeTable, hx]
      simp only [hl, hr]
      exact ih _ m L W₀ (ht _) (by omega)
    · -- a new query: split off the fresh value on both sides
      have hℓ : L.length < q := by omega
      have hidx : (L ++ [x]).idxOf x = L.length := by
        rw [List.idxOf_append_of_notMem hx]; simp
      have hlen : (L ++ [x]).length = L.length + 1 := by simp
      let j : Fin q := ⟨L.length, hℓ⟩
      let g : O → (Fin q → O) → Prop := fun v W =>
        φ (evalLazy (extendStream (combine (L ++ [x]).length (update W₀ j v) W)) (k v)
          (L ++ [x]))
      let h : O → (I → O) → Prop := fun v R =>
        φ ((k v).eval (mergeTable (L ++ [x]) (extendStream (update W₀ j v)) R))
      have hl : ∀ W, φ (evalLazy (extendStream (combine L.length W₀ W)) (query x k) L) ↔
          g (W j) W := by
        intro W
        simp only [g, evalLazy_query, noteQuery_of_not_mem hx, hidx, hlen,
          extendStream_combine_self _ _ hℓ, ← combine_succ _ _ hℓ, j]
      have hr : ∀ R, φ ((query x k).eval (mergeTable L (extendStream W₀) R)) ↔
          h (R x) R := by
        intro R
        simp only [h, eval_query, ← mergeTable_append W₀ R hx hℓ, j]
        simp [mergeTable, hx]
      rw [uprob_congr hl, uprob_congr hr,
        uprob_update_split j g (fun v W u => by simp only [g, hlen, j, combine_update]),
        uprob_update_split x h (fun v R u => by
          simp only [h, mergeTable_update _ _ _ (List.mem_append_right L
            (List.mem_singleton_self x))])]
      exact congrArg uexp (funext fun v =>
        ih v m (L ++ [x]) (update W₀ j v) (ht v) (by rw [hlen]; omega))

/-- **Lazy sampling.** For a query tree making at most `q` queries, answering the `k`-th
distinct query by the `k`-th of `q` independent uniform values gives the same output
distribution as answering by a uniform random function. [Gar26, §3.4.2, footnote 9],
stated as an exact equality of probabilities for every event on the output.

**Proof sketch.** Generalize to a run started with a list `L` of `ℓ` distinct queries
whose answers are fixed values `W₀`, against a random function that agrees with `W₀` on
`L`. A repeated query is answered by the fixed value on both sides. A new query is
answered by the fresh value `W ℓ` on the lazy side and by `R x` on the table side; in
both cases the rest of the run does not read this entry again except through the
recorded answer, so both probabilities are the average over the answer `v` of the
probability of the continuation with `v` recorded, which agree by induction. -/
theorem uprob_evalLazy [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {t : QueryTree I O α} {q : ℕ} (ht : t.BoundedBy q) :
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream W) t [])) =
      uprob (fun R : I → O => φ (t.eval R)) := by
  have h := uprob_evalLazy_aux (q := q) φ t q [] (fun _ => Classical.arbitrary O) ht (by simp)
  have h1 : ∀ W : Fin q → O, combine ([] : List I).length (fun _ => Classical.arbitrary O) W = W :=
    fun W => funext fun i => by simp [combine]
  have h2 : ∀ R : I → O, mergeTable [] (extendStream fun _ : Fin q => Classical.arbitrary O)
      R = R := fun R => funext fun y => by simp [mergeTable]
  simpa only [h1, h2] using h

end QueryTree

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive oracle adversaries as query trees

An oracle adversary asks its oracle a question, looks at the answer, chooses the next
question, and finally outputs a value. At one fixed value of the security parameter such
an adversary (for a fixed coin string) is exactly a finite tree: a leaf carries the output,
and an inner node carries a query `x : I` and one subtree for each possible answer `o : O`.
The coins are a uniform element of a finite type `ρ`, so a randomized oracle adversary is a
function `ρ → QueryTree I O α`.

Running the adversary against an oracle `f : I → O` follows the path chosen by the
answers `f x`. The adversary makes at most `q` queries when every root-to-leaf path has at
most `q` inner nodes. The cost of a query in [Gar26, Definition 3.9] ("each call to that
function costs 1 unit of time") is accounted by this bound; running time otherwise is the
business of the asymptotic layer.

Answering the queries of one adversary by a computation that itself asks queries to a
second oracle (`simulate`) is the basic reduction step: the simulated tree makes the same
number of queries.

**One notion of oracle computation** (ruling of 2026-11-05, item F-1). A query tree *is* a
computation of the `Games` framework with one oracle: `QueryTree I O α` abbreviates
`Games.OracleComp (Games.singleSpec I O) α`, and `ret` and `query` are its two constructors (the
oracle index is the unit). Definitions by cases on `ret`/`query` are unchanged; proofs by
induction use `QueryTree.induct`. The links of `eval`, `BoundedBy` and `simulate` to the
framework's evaluation, query costs and simulation are in
`TCSlib.Cryptography.Games.Bridges.QueryTree`.

**Deviation:** query, answer and output types are in `Type` (universe 0), as the framework's are;
every use in [Gar26] and [PS10] is at `Type`.

## Main definitions

* `QueryTree I O α`: adaptive query trees with queries in `I`, answers in `O` and outputs
  in `α`: the one-oracle computations of the `Games` framework.
* `QueryTree.induct`: induction on query trees by their two constructors.
* `QueryTree.eval f t`: the output of `t` run against the oracle `f`.
* `QueryTree.BoundedBy t q`: every path of `t` makes at most `q` queries.
* `QueryTree.simulate π ans t`: answer each query `x` of `t` by asking `π x` to a new oracle
  and post-processing the answer with `ans x`.
* `OracleAdversary ρ I O`: randomized Boolean oracle adversaries with coins in `ρ`.
* `oracleDist A`: the adversary viewed as a distinguisher for oracles.

## Main results

* `QueryTree.eval_simulate`: running the simulated tree against `g` is running the
  original tree against the oracle `x ↦ ans x (g (π x))`.
* `QueryTree.BoundedBy.simulate`: simulation preserves the query bound.
* `QueryTree.BoundedBy.mono`: query bounds are monotone.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 3.9 (oracle adversaries).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle computations as a
  free monad over an indexed oracle specification (`VCVio/OracleComp/OracleComp.lean`), here
  through `TCSlib.Cryptography.Games.OracleComp`.
-/

namespace TCSlib.Cryptography


/-- An adaptive oracle algorithm with queries in `I`, answers in `O` and output in `α`,
as a decision tree: `ret a` stops and outputs `a`, and `query x k` asks the oracle at `x`
and continues with the subtree `k o` for the answer `o`. This is the concrete form of an
oracle adversary with fixed coins [Gar26, Definition 3.9]: the one-oracle computation of the
`Games` framework. [VCVio, OracleComp/OracleComp] -/
abbrev QueryTree (I O α : Type) : Type := Games.OracleComp (Games.singleSpec I O) α

namespace QueryTree

variable {I O α I' O' : Type}

/-- Stop and output `a`. -/
@[match_pattern] abbrev ret (a : α) : QueryTree I O α := Games.OracleComp.pure a

/-- Ask the oracle at `x` and continue with `k` applied to the answer. -/
@[match_pattern] abbrev query (x : I) (k : O → QueryTree I O α) : QueryTree I O α :=
  Games.OracleComp.query () x k

/-- **Induction on query trees** by their two constructors: a property of leaves, and the step
from all the subtrees of a query to the query. Use it as `induction t using QueryTree.induct`. -/
@[elab_as_elim] def induct {motive : QueryTree I O α → Sort _} (ret : ∀ a, motive (ret a))
    (query : ∀ x k, (∀ o, motive (k o)) → motive (query x k)) : ∀ t, motive t
  | Games.OracleComp.pure a => ret a
  | Games.OracleComp.query () x k => query x k fun o => induct ret query (k o)

/-- `induct` computes on a leaf by its leaf case: `induct hret hquery (ret a) = hret a`. -/
theorem induct_ret {motive : QueryTree I O α → Sort _} (hret : ∀ a, motive (ret a))
    (hquery : ∀ x k, (∀ o, motive (k o)) → motive (query x k)) (a : α) :
    induct (motive := motive) hret hquery (ret a) = hret a :=
  rfl

/-- `induct` computes on a query node by its query case, applied to the inductions on the
subtrees: `induct hret hquery (query x k) = hquery x k (fun o => induct hret hquery (k o))`. -/
theorem induct_query {motive : QueryTree I O α → Sort _} (hret : ∀ a, motive (ret a))
    (hquery : ∀ x k, (∀ o, motive (k o)) → motive (query x k)) (x : I)
    (k : O → QueryTree I O α) :
    induct (motive := motive) hret hquery (query x k) =
      hquery x k fun o => induct (motive := motive) hret hquery (k o) :=
  rfl

/-- The output of the query tree `t` when every query `x` is answered by `f x`. -/
def eval (f : I → O) : QueryTree I O α → α
  | ret a => a
  | query x k => eval f (k (f x))

/-- A leaf outputs its value. -/
@[simp] theorem eval_ret (f : I → O) (a : α) : (ret a : QueryTree I O α).eval f = a := rfl

/-- A query node continues with the subtree for the oracle's answer. -/
@[simp] theorem eval_query (f : I → O) (x : I) (k : O → QueryTree I O α) :
    (query x k).eval f = (k (f x)).eval f := rfl

/-- The query tree `t` makes at most `q` oracle queries along every path: a leaf is
bounded by every `q`, and `query x k` is bounded by `q + 1` when every continuation `k o`
is bounded by `q`. -/
def BoundedBy : QueryTree I O α → ℕ → Prop
  | ret _, _ => True
  | query _ _, 0 => False
  | query _ k, q + 1 => ∀ o, BoundedBy (k o) q

/-- A leaf makes no queries. -/
@[simp] theorem boundedBy_ret (a : α) (q : ℕ) : (ret a : QueryTree I O α).BoundedBy q :=
  trivial

/-- A query node makes at least one query. -/
@[simp] theorem boundedBy_query_zero (x : I) (k : O → QueryTree I O α) :
    ¬ (query x k).BoundedBy 0 := id

/-- A query node makes at most `q + 1` queries iff every continuation makes at most
`q`. -/
@[simp] theorem boundedBy_query_succ (x : I) (k : O → QueryTree I O α) (q : ℕ) :
    (query x k).BoundedBy (q + 1) ↔ ∀ o, (k o).BoundedBy q := Iff.rfl

/-- A tree making at most `q` queries makes at most `q'` queries for every `q' ≥ q`. -/
theorem BoundedBy.mono {t : QueryTree I O α} {q q' : ℕ} (h : t.BoundedBy q)
    (hq : q ≤ q') : t.BoundedBy q' := by
  induction t using QueryTree.induct generalizing q q' with
  | ret a => trivial
  | query x k ih =>
    cases q with
    | zero => exact absurd h (boundedBy_query_zero x k)
    | succ q =>
      obtain ⟨q', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      exact fun o => ih o (h o) (by omega)

/-- Simulation of oracle queries: each query `x` of `t` is replaced by the query `π x` to a
new oracle with answers in `O'`, whose answer `o'` is turned into the answer `ans x o'` for
`t`. The simulated tree asks exactly one new query per original query. -/
def simulate (π : I → I') (ans : I → O' → O) : QueryTree I O α → QueryTree I' O' α
  | ret a => ret a
  | query x k => query (π x) (fun o' => simulate π ans (k (ans x o')))

/-- Simulating a leaf leaves it unchanged: `(ret a).simulate π ans = ret a`. -/
theorem simulate_ret (π : I → I') (ans : I → O' → O) (a : α) :
    (ret a : QueryTree I O α).simulate π ans = ret a :=
  rfl

/-- Simulating a query node asks `π x` and continues, on the answer `o'`, with the simulation of
the subtree for `ans x o'`:
`(query x k).simulate π ans = query (π x) (fun o' => (k (ans x o')).simulate π ans)`. -/
theorem simulate_query (π : I → I') (ans : I → O' → O) (x : I) (k : O → QueryTree I O α) :
    (query x k).simulate π ans = query (π x) (fun o' => (k (ans x o')).simulate π ans) :=
  rfl

/-- Running the simulated tree against `g` is running the original tree against the
oracle that answers `x` by `ans x (g (π x))`. -/
@[simp] theorem eval_simulate (π : I → I') (ans : I → O' → O) (g : I' → O')
    (t : QueryTree I O α) :
    (t.simulate π ans).eval g = t.eval (fun x => ans x (g (π x))) := by
  induction t using QueryTree.induct with
  | ret a => rfl
  | query x k ih => exact ih _

/-- Simulation does not increase the number of queries. -/
theorem BoundedBy.simulate {t : QueryTree I O α} {q : ℕ} (h : t.BoundedBy q)
    (π : I → I') (ans : I → O' → O) : (t.simulate π ans).BoundedBy q := by
  induction t using QueryTree.induct generalizing q with
  | ret a => trivial
  | query x k ih =>
    cases q with
    | zero => exact absurd h (boundedBy_query_zero x k)
    | succ q => exact fun o' => ih _ (h _)

end QueryTree

/-- A randomized Boolean oracle adversary with coins in `ρ`: for every coin string a query
tree with queries in `I`, answers in `O` and a one-bit output. [Gar26, Definition 3.9]
at one value of the security parameter; the input `1^n` is implicit in the fixed types,
and the coins are uniform over the finite type `ρ`. -/
abbrev OracleAdversary (ρ : Type*) (I O : Type) := ρ → QueryTree I O Bool

/-- The randomized oracle adversary `A` makes at most `q` queries on every coin string and
every path. -/
def OracleAdversary.BoundedBy {ρ : Type*} {I O : Type}
    (A : OracleAdversary ρ I O) (q : ℕ) : Prop :=
  ∀ r, (A r).BoundedBy q

/-- The oracle adversary `A` as a distinguisher for oracles: on the oracle `f` and coins
`r` it outputs the result of running `A r` against `f`. With a sampler for the oracle,
`acceptProb` of this distinguisher is the probability `Pr[A^f = 1]` of
[Gar26, Definition 3.9]. -/
def oracleDist {ρ : Type*} {I O : Type} (A : OracleAdversary ρ I O) :
    (I → O) → ρ → Bool :=
  fun f r => (A r).eval f

/-- The distinguisher of `A` on the oracle `f` and coins `r` is the run of `A r` against `f`:
`oracleDist A f r = (A r).eval f`. -/
theorem oracleDist_apply {ρ : Type*} {I O : Type} (A : OracleAdversary ρ I O) (f : I → O)
    (r : ρ) : oracleDist A f r = (A r).eval f :=
  rfl

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import TCSlib.Cryptography.Pseudorandom.Functions.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sub-hybrids: a table of PRG outputs against an adaptive adversary

This file isolates the inner hybrid argument of the GGM proof [Gar26, proof of
Theorem 3.3, "Sub-hybrids"]. Let `G : S → V` be a generator and consider an oracle
adversary `A` making at most `q` queries to a table `T : P → V`. In the *pseudorandom*
world the table is `G ∘ R` for a uniform `R : P → S`; in the *random* world it is a
uniform `T : P → V`. We bound the gap by `q` PRG distinguishing advantages.

The sub-hybrid `H_j` (`subHybridProb G A q j`) answers the queries lazily: the `k`-th
distinct query is answered by a uniform value of `V` if `k < j` and by `G` of a uniform
seed otherwise. So `H_0` is the pseudorandom world and `H_q` the random world, by lazy
sampling (`QueryTree.uprob_evalLazy`). The PRG distinguisher `tableDist G A q j` embeds
its challenge `z ∈ V` as the answer to the `j`-th distinct query; it accepts with the
probability of `H_j` when `z = G(s)` and with that of `H_{j+1}` when `z` is uniform.

**Deviation from the source.** [Gar26] defines `H_{i,j}` through a list `L` of prefixes,
which amounts to answering the first `j` *distinct* prefixes randomly, as here. The
argument then speaks of "the `(j*+1)`-th query", claims that it cannot repeat an earlier
prefix "because otherwise the hybrids would be identical" (not a valid inference: two
hybrids can differ although they agree on a particular event), and has the outer
adversary answer only that one query with its challenge, which leaves later queries with
the same prefix inconsistent with the challenge. Here the sub-hybrids are indexed by
distinct queries in order of first appearance, and the distinguisher answers *every*
query equal to the `j`-th distinct one with the challenge. A repeated query is then
simply answered by its recorded value, so no case split on repeats is needed, and the
distinguisher's runs coincide pointwise with those of the hybrids after relabelling one
uniform coordinate.

## Main definitions

* `subHybridStream G j W`, `subHybridProb G A q j`: the sub-hybrid `H_j`.
* `tableDist G A q j`: the PRG distinguisher embedding its challenge at the `j`-th
  distinct query.

## Main results

* `acceptProb_tableDist_prg`, `acceptProb_tableDist_uniform`: the distinguisher realises
  `H_j` and `H_{j+1}`.
* `subHybridProb_zero`, `subHybridProb_top`: the endpoints are the pseudorandom and the
  random table.
* `table_hybrid`: the gap between the two worlds is at most the sum over `j < q` of the
  distinguishing advantages of `tableDist G A q j`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, proof of Theorem 3.3 (sub-hybrids `H_{i,j}` and the
  outer adversary `B`), footnote 9 (lazy sampling).
-/

namespace TCSlib.Cryptography

open Function QueryTree

attribute [local irreducible] uprob acceptProb

variable {P S V : Type} {ρ : Type*} [Fintype P] [DecidableEq P] [Fintype S] [Nonempty S]
  [Fintype V] [Nonempty V] [Fintype ρ]

/-- The answer stream of the sub-hybrid `H_j` [Gar26, proof of Theorem 3.3]: the `k`-th
distinct query is answered by the uniform value `W.2 k` if `k < j` and by the generator
output `G (W.1 k)` on a uniform seed otherwise. -/
noncomputable def subHybridStream {q : ℕ} (G : S → V) (j : ℕ)
    (W : (Fin q → S) × (Fin q → V)) : ℕ → V :=
  fun k => if k < j then extendStream W.2 k else G (extendStream W.1 k)

/-- The oracle adversary `A` run with lazily sampled answers given by an answer stream. -/
def lazyDist (A : OracleAdversary ρ P V) : (ℕ → V) → ρ → Bool :=
  fun a r => (A r).evalLazy a []

/-- The probability that `A` accepts in the sub-hybrid `H_j`: `j` uniform values and
`q - j` generator outputs answer the distinct queries in order. [Gar26, proof of
Theorem 3.3, `H_{i,j}`] with the level `i` abstracted away; see the module docstring for
the indexing by distinct queries. -/
noncomputable def subHybridProb (G : S → V) (A : OracleAdversary ρ P V) (q j : ℕ) : ℝ :=
  acceptProb (subHybridStream (q := q) G j) (lazyDist A)

/-- The answer stream of the PRG distinguisher: as in `H_j`, except that the `j`-th
distinct query is answered by the challenge `z`. -/
noncomputable def challengeStream {q : ℕ} (G : S → V) (j : ℕ) (z : V)
    (W : (Fin q → S) × (Fin q → V)) : ℕ → V :=
  fun k => if k < j then extendStream W.2 k else if k = j then z else G (extendStream W.1 k)

/-- The PRG distinguisher built from the oracle adversary `A` [Gar26, proof of
Theorem 3.3, the outer adversary `B`]. On a challenge `z ∈ V` and coins
`((W₀, W₁), r)` with `W₀ : Fin q → S`, `W₁ : Fin q → V`, it runs `A` once on coins `r`,
answers the `k`-th distinct query by `W₁ k` if `k < j`, by `z` if `k = j`, and by
`G (W₀ k)` if `k > j`, and outputs what `A` outputs.

*Cost*, for `A` bounded by `q` queries (`OracleAdversary.BoundedBy`; the definition itself
runs any `A`). One run of `A`; at most `q` evaluations of `G`; `q` seeds and `q` values of
fresh randomness (lazy sampling, [Gar26, footnote 9]: no exponential table is sampled);
bookkeeping of the list of at most `q` distinct queries (membership and position
lookups). -/
noncomputable def tableDist (G : S → V) (A : OracleAdversary ρ P V) (q j : ℕ) :
    V → ((Fin q → S) × (Fin q → V)) × ρ → Bool :=
  fun z c => (A c.2).evalLazy (challengeStream G j z c.1) []

omit [Fintype P] in
/-- On a pseudorandom challenge `z = G s` the distinguisher `tableDist G A q j` accepts
exactly with the probability of the sub-hybrid `H_j`, for `j < q`.

**Proof sketch.** With `z = G s`, the challenge stream is the stream of `H_j` with the
seed table `W₀` overwritten at position `j` by `s`; overwriting one entry of a uniform
table by a uniform value leaves it uniform. -/
theorem acceptProb_tableDist_prg (G : S → V) (A : OracleAdversary ρ P V) {q j : ℕ}
    (hj : j < q) : acceptProb G (tableDist G A q j) = subHybridProb G A q j := by
  have hs : ∀ (s : S) (W : (Fin q → S) × (Fin q → V)),
      challengeStream G j (G s) W = subHybridStream G j (update W.1 ⟨j, hj⟩ s, W.2) := by
    intro s W; funext k
    unfold challengeStream subHybridStream
    by_cases h1 : k < j
    · simp [h1]
    · by_cases h2 : k = j
      · subst h2; simp only [lt_irrefl, if_false, if_true]
        exact congrArg G (extendStream_update_self W.1 ⟨k, hj⟩ s).symm
      · rw [if_neg h1, if_neg h1, if_neg h2, extendStream_update_of_ne _ _ _ h2]
  let E : (Fin q → S) → (Fin q → V) × ρ → Prop :=
    fun W₀ c => (A c.2).evalLazy (subHybridStream G j (W₀, c.1)) [] = true
  let e : S × ((Fin q → S) × ((Fin q → V) × ρ)) ≃ S × (((Fin q → S) × (Fin q → V)) × ρ) :=
    (Equiv.refl S).prodCongr (Equiv.prodAssoc _ _ _).symm
  have h1 : acceptProb G (tableDist G A q j) =
      uprob (fun z : S × ((Fin q → S) × ((Fin q → V) × ρ)) =>
        E (update z.2.1 ⟨j, hj⟩ z.1) z.2.2) := by
    rw [acceptProb, ← uprob_comp_equiv e
      (fun z : S × (((Fin q → S) × (Fin q → V)) × ρ) => tableDist G A q j (G z.1) z.2 = true)]
    exact uprob_congr fun z => iff_of_eq
      (congrArg (fun a => (A z.2.2.2).evalLazy a [] = true) (hs z.1 (z.2.1, z.2.2.1)))
  have h2 : subHybridProb G A q j = uprob (fun z : (Fin q → S) × ((Fin q → V) × ρ) => E z.1 z.2) := by
    rw [subHybridProb, acceptProb, ← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm
      (fun z : ((Fin q → S) × (Fin q → V)) × ρ => lazyDist A (subHybridStream G j z.1) z.2 = true)]
    rfl
  rw [h1, h2]
  exact uprob_update_absorb _ E

omit [Fintype P] in
/-- On a uniform challenge `z` the distinguisher `tableDist G A q j` accepts exactly
with the probability of the sub-hybrid `H_{j+1}`, for `j < q`.

**Proof sketch.** With `z` uniform, the challenge stream is the stream of `H_{j+1}` with
the uniform value table `W₁` overwritten at position `j` by `z`, which is again
uniform. -/
theorem acceptProb_tableDist_uniform (G : S → V) (A : OracleAdversary ρ P V) {q j : ℕ}
    (hj : j < q) :
    acceptProb (id : V → V) (tableDist G A q j) = subHybridProb G A q (j + 1) := by
  have hs : ∀ (z : V) (W : (Fin q → S) × (Fin q → V)),
      challengeStream G j z W = subHybridStream G (j + 1) (W.1, update W.2 ⟨j, hj⟩ z) := by
    intro z W; funext k
    unfold challengeStream subHybridStream
    by_cases h1 : k < j
    · rw [if_pos h1, if_pos (by omega), extendStream_update_of_ne _ _ _ (by simp; omega)]
    · by_cases h2 : k = j
      · subst h2; simp only [lt_irrefl, Nat.lt_succ_self, if_false, if_true]
        exact (extendStream_update_self W.2 ⟨k, hj⟩ z).symm
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]
  let E : (Fin q → V) → (Fin q → S) × ρ → Prop :=
    fun W₁ c => (A c.2).evalLazy (subHybridStream G (j + 1) (c.1, W₁)) [] = true
  let e : V × ((Fin q → V) × ((Fin q → S) × ρ)) ≃ V × (((Fin q → S) × (Fin q → V)) × ρ) :=
    (Equiv.refl V).prodCongr
      { toFun := fun c => ((c.2.1, c.1), c.2.2)
        invFun := fun c => (c.1.2, (c.1.1, c.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let e' : (Fin q → V) × ((Fin q → S) × ρ) ≃ ((Fin q → S) × (Fin q → V)) × ρ :=
    { toFun := fun c => ((c.2.1, c.1), c.2.2)
      invFun := fun c => (c.1.2, (c.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : acceptProb (id : V → V) (tableDist G A q j) =
      uprob (fun z : V × ((Fin q → V) × ((Fin q → S) × ρ)) =>
        E (update z.2.1 ⟨j, hj⟩ z.1) z.2.2) := by
    rw [acceptProb, ← uprob_comp_equiv e
      (fun z : V × (((Fin q → S) × (Fin q → V)) × ρ) => tableDist G A q j (id z.1) z.2 = true)]
    exact uprob_congr fun z => iff_of_eq
      (congrArg (fun a => (A z.2.2.2).evalLazy a [] = true) (hs z.1 (z.2.2.1, z.2.1)))
  have h2 : subHybridProb G A q (j + 1) =
      uprob (fun z : (Fin q → V) × ((Fin q → S) × ρ) => E z.1 z.2) := by
    rw [subHybridProb, acceptProb, ← uprob_comp_equiv e'
      (fun z : ((Fin q → S) × (Fin q → V)) × ρ =>
        lazyDist A (subHybridStream G (j + 1) z.1) z.2 = true)]
    rfl
  rw [h1, h2]
  exact uprob_update_absorb _ E

/-- The sub-hybrid `H_0` is the pseudorandom table: for an adversary making at most `q`
queries, answering every distinct query by `G` of a fresh seed is the same as querying
`G ∘ R` for a uniform `R : P → S`. [Gar26, proof of Theorem 3.3, "`H_{i,0}` is the same
as `H_i`"].

**Proof sketch.** Condition on the adversary's coins; post-compose the tree's answers
with `G` and apply lazy sampling for seeds. -/
theorem subHybridProb_zero (G : S → V) (A : OracleAdversary ρ P V) {q : ℕ}
    (hA : A.BoundedBy q) :
    subHybridProb G A q 0 = acceptProb (fun R : P → S => G ∘ R) (oracleDist A) := by
  have h1 : subHybridProb G A q 0 = uprob (fun z : ρ × ((Fin q → S) × (Fin q → V)) =>
      ((A z.1).simulate id (fun _ => G)).evalLazy (extendStream z.2.1) [] = true) := by
    rw [subHybridProb, acceptProb]
    refine (uprob_prod_comm (fun W r => lazyDist A (subHybridStream G 0 W) r = true)).trans
      (uprob_congr fun z => iff_of_eq ?_)
    have hs : subHybridStream G 0 z.2 = G ∘ extendStream z.2.1 := by
      funext k; simp [subHybridStream]
    rw [lazyDist, hs, evalLazy_comp]
  have h2 : acceptProb (fun R : P → S => G ∘ R) (oracleDist A) =
      uprob (fun z : ρ × (P → S) => ((A z.1).simulate id (fun _ => G)).eval z.2 = true) := by
    rw [acceptProb]
    refine (uprob_prod_comm (fun R r => oracleDist A (G ∘ R) r = true)).trans
      (uprob_congr fun z => iff_of_eq ?_)
    rw [eval_simulate]; rfl
  rw [h1, h2]
  refine uprob_sections_congr
    (fun r (W : (Fin q → S) × (Fin q → V)) =>
      ((A r).simulate id (fun _ => G)).evalLazy (extendStream W.1) [] = true)
    (fun r (R : P → S) => ((A r).simulate id (fun _ => G)).eval R = true) fun r => ?_
  exact (uprob_fst (fun W : Fin q → S =>
    ((A r).simulate id (fun _ => G)).evalLazy (extendStream W) [] = true)).trans
    (uprob_evalLazy (· = true) ((hA r).simulate _ _))

/-- The sub-hybrid `H_q` is the random table: for an adversary making at most `q`
queries, all its distinct queries are answered by fresh uniform values, which is the same
as querying a uniform random function `P → V`. [Gar26, proof of Theorem 3.3, "`H_{i,q}`
is the same as `H_{i+1}`"].

**Proof sketch.** The adversary never reaches a `q`-th distinct query, so the stream of
`H_q` may be replaced by the uniform values alone; then condition on the coins and apply
lazy sampling. -/
theorem subHybridProb_top (G : S → V) (A : OracleAdversary ρ P V) {q : ℕ}
    (hA : A.BoundedBy q) :
    subHybridProb G A q q = acceptProb (randomFunction P V) (oracleDist A) := by
  have h1 : subHybridProb G A q q = uprob (fun z : ρ × ((Fin q → S) × (Fin q → V)) =>
      (A z.1).evalLazy (extendStream z.2.2) [] = true) := by
    rw [subHybridProb, acceptProb]
    refine (uprob_prod_comm (fun W r => lazyDist A (subHybridStream G q W) r = true)).trans
      (uprob_congr fun z => iff_of_eq ?_)
    rw [lazyDist]
    congr 1
    exact evalLazy_congr (hA z.1) [] fun k hk => if_pos (by simpa using hk)
  have h2 : acceptProb (randomFunction P V) (oracleDist A) =
      uprob (fun z : ρ × (P → V) => (A z.1).eval z.2 = true) := by
    rw [acceptProb]
    exact uprob_prod_comm (fun T r => oracleDist A (randomFunction P V T) r = true)
  rw [h1, h2]
  refine uprob_sections_congr
    (fun r (W : (Fin q → S) × (Fin q → V)) => (A r).evalLazy (extendStream W.2) [] = true)
    (fun r (T : P → V) => (A r).eval T = true) fun r => ?_
  exact (uprob_snd (fun W : Fin q → V => (A r).evalLazy (extendStream W) [] = true)).trans
    (uprob_evalLazy (· = true) (hA r))

/-- **Sub-hybrid argument.** For an adversary making at most `q` queries to a table, the
gap between the pseudorandom table `G ∘ R` and a uniform table is at most the sum over
`j < q` of the PRG distinguishing advantages of `tableDist G A q j`, with `G` of a
uniform seed against a uniform element of `V`. [Gar26, proof of Theorem 3.3, sub-hybrids
`H_{i,0}, …, H_{i,q}` at one level], an exact inequality.

**Proof sketch.** The endpoints are `H_0` and `H_q`; telescope, and identify each
neighbouring gap `|H_j - H_{j+1}|` with the advantage of `tableDist G A q j`. -/
theorem table_hybrid (G : S → V) (A : OracleAdversary ρ P V) {q : ℕ} (hA : A.BoundedBy q) :
    |acceptProb (fun R : P → S => G ∘ R) (oracleDist A) -
        acceptProb (randomFunction P V) (oracleDist A)| ≤
      ∑ j : Fin q, distAdv G (id : V → V) (tableDist G A q j) := by
  rw [← subHybridProb_zero G A hA, ← subHybridProb_top G A hA]
  have key := abs_sub_le_sum_hybrids (fun j => subHybridProb G A q j) q
  have hsum : ∑ i ∈ Finset.range q, |subHybridProb G A q i - subHybridProb G A q (i + 1)| =
      ∑ j : Fin q, distAdv G (id : V → V) (tableDist G A q j) := by
    rw [Finset.sum_range (fun j => |subHybridProb G A q j - subHybridProb G A q (j + 1)|)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := acceptProb_tableDist_prg G A j.isLt
    have h2 := acceptProb_tableDist_uniform G A j.isLt
    unfold distAdv
    rw [h1, h2]
  exact key.trans hsum.le

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Interaction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive protocols: strategies, executions, views

The interaction model of [PS10, §4.4] in the form frozen by the campaign's foundation
decision D8 (`briefs/pass-shelat/DESIGN.md` §2.15). An interactive machine is a *next-message
strategy* `next x z r received`: given the common input `x`, the auxiliary input `z`, the
random tape `r` and the messages received so far, it returns the next message to send; its
value on the complete history is the party's output. A protocol is a pair of strategies with
an explicit polynomial number of messages (`rounds : PolyExpr`) and a first mover. The
execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)` is the fixed alternation of `rounds.eval |x|` moves
(`exec`), and the four derived objects of the text — the view of each party, the transcript,
and the outputs — are projections of it.

**Deviation (D8, recorded once here for the whole chapter):** no tapes, states or idle
transitions are modelled; "entering the idle state" is returning from `next`; the number of
messages is fixed by the protocol (a party that would halt is modelled as sending `[]`), and the
verifier's verdict is `V.next` on the complete history, so it is always defined. The text's
"a round ends when the active machine halts — in which case the protocol ends" makes the
literal `Pr[out_V = 0]` of [PS10, Definition 116.1] unsatisfiable against a prover that halts
at once; the fixed-alternation reading is the one under which that clause is satisfiable.
Verdict convention (run-3 audit P9-3): when the verifier is the last mover, the verdict
activation has exactly the arguments of the activation that produced its last message, so its
last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chapter's protocols
are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
message as the verdict.
`Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
whole random tape; the time is polynomial in the total input length rather than in `|x|`
alone (the text's `t(|x|)` "regardless of messages" would leave the simulator's call to `V*`
on long auxiliary inputs ill-defined; see D8). Consequently `Efficient` alone does not bound a
party's work in `|x|` against a counterparty that sends long messages; the message-prefix cap
`Strategy.ReadsPrefix m` — the strategy depends only on the first `m(|x|)` bits of each received
message, as a time-`t(|x|)` machine of the text necessarily does — restores the text's bound,
and the class `IP` (`InteractiveProofs.lean`) requires it of the verifier (run-3 audit P9-1).

## Main definitions

* `TCSlib.Cryptography.Strategy` — a next-message strategy with an explicit coin polynomial
  [PS10, §4.4] (Def-114.a); `Strategy.ofNUPPT`, `Strategy.Efficient` (Def-116.b, the machine
  half), `Strategy.ReadsPrefix` (Def-116.b, the message-prefix cap of the text's bound in `|x|`).
* `TCSlib.Cryptography.exec` — the messages received by each party after `k` moves
  [PS10, §4.4] (Def-115.a).
* `TCSlib.Cryptography.View`, `TCSlib.Cryptography.View.encode` — a party's view
  `(x, z, r, received)` and its string encoding (Def-115.b).
* `TCSlib.Cryptography.Protocol` — two strategies, the number of messages and the first mover
  (Def-114.b); `Protocol.transcriptWith`, `Protocol.transcript` (Def-115.c), `Protocol.outV`,
  `Protocol.outP`, `Strategy.out` (Def-115.d), `Protocol.viewV`, `Protocol.viewP`,
  `Protocol.execution` (Def-115.a/b), `Protocol.withV`.

## Main results

* `TCSlib.Cryptography.exec_length` — after `k` moves exactly `k` messages have been sent.
* `TCSlib.Cryptography.Strategy.ofNUPPT_efficient` — every uniform machine is an efficient
  strategy (non-vacuity of Def-116.b).
* `TCSlib.Cryptography.Strategy.ReadsPrefix.mono`,
  `TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr` — the message-prefix cap is monotone
  in the cap and makes the next message a function of the truncated history.
* `TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV` — when the verifier is the last
  mover, its last message is its verdict (the verdict convention of D8).
* `TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp`,
  `TCSlib.Cryptography.Protocol.exists_proverCoins_le` — random executions are samplers on the
  product of the two coin spaces (Def-116.a), and a prover's coins may be fixed without
  decreasing any event's probability (the "without loss of generality deterministic `P*`"
  remark of the soundness clause).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.4 Interactive protocols, pp. 114–116.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, interactive proofs.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Strategies -/

/-- A next-message strategy [PS10, §4.4] (Def-114.a): `next x z r received` is the message a
party sends on common input `x`, auxiliary input `z` and random tape `r` after having
*received* the listed messages; on the complete history its value is the party's output. The
random tape has the explicit polynomial length `coins.eval |x|`.

**Deviation (D8):** no tapes, states or idle transitions; the output function of the text is
the next-message function on the complete history. -/
structure Strategy where
  /-- The next-message function `(x, z, r, received) ↦ message`. -/
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool
  /-- The length of the random tape as a polynomial in `|x|`. -/
  coins : PolyExpr

namespace Strategy

/-- The number of random bits of a strategy at common-input length `n`. -/
def coinLen (S : Strategy) (n : ℕ) : ℕ := S.coins.eval n

/-- The random tape of a strategy at common-input length `n`: `coinLen n` uniform bits. -/
abbrev Coins (S : Strategy) (n : ℕ) : Type := Fin (S.coinLen n) → Bool

/-- The string encoding of a list of messages: right-nested `pairEncode` pairs ending in `[]`
(the encoding of the received-messages component of a view, Inf-4.1). -/
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

/-- The encoding of the empty history is the empty string. -/
@[simp] theorem encodeMsgs_nil : encodeMsgs [] = [] := rfl

/-- The encoding of `m :: h` is the pair `⟨m, encodeMsgs h⟩`. -/
@[simp] theorem encodeMsgs_cons (m : List Bool) (h : List (List Bool)) :
    encodeMsgs (m :: h) = pairEncode m (encodeMsgs h) := rfl

/-- The first projection of an encoded history is its first message (`[]` when empty). -/
theorem pairFstD_encodeMsgs (h : List (List Bool)) : pairFstD (encodeMsgs h) = h.headD [] := by
  cases h with
  | nil => rfl
  | cons m h => simp

/-- The strategy computed by a machine `A`: one activation at parameter `|x|` on
`⟨⟨x, z⟩, messages⟩` with the whole random tape (`A.runAtL`); the coin polynomial is `A.coins`
[PS10, §4.4, the interactive machine as a Turing machine with a random tape]. -/
def ofNUPPT (A : NUPPT) : Strategy where
  next x z r hist := A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r
  coins := A.coins

/-- The next-message function of `ofNUPPT A` unfolds to one activation of `A`. -/
theorem ofNUPPT_next (A : NUPPT) (x z r : List Bool) (hist : List (List Bool)) :
    (ofNUPPT A).next x z r hist =
      A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r := rfl

/-- A PPT strategy [PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the
next-message function is computed by a uniform `NUPPT` with the same coin polynomial, one
activation per message at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.

**Deviation (D8):** per-activation time polynomial in the total input length `|x| + |z| +
|messages|` instead of the text's `t(|x|)` "regardless of the messages". The number of
activations is bounded by the protocol's `rounds`, but the messages of an unbounded
counterparty may be arbitrarily long, so `Efficient` alone does not bound a party's work in
`|x|` (run-3 audit P9-1). The text's bound is recovered by adding the message-prefix cap
`ReadsPrefix m`: an efficient strategy that reads only `m(|x|)` bits of each message runs in
time polynomial in `|x| + |z|`, and the class `IP` requires the cap of the verifier. -/
def Efficient (S : Strategy) : Prop :=
  ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧
    ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist

/-- Non-vacuity of `Strategy.Efficient`: the strategy of a uniform machine is efficient. -/
theorem ofNUPPT_efficient (A : NUPPT) (hA : A.Uniform) : (ofNUPPT A).Efficient :=
  ⟨A, hA, rfl, fun _ _ _ _ => rfl⟩

/-- An efficient strategy has the coin polynomial of some uniform machine computing it. -/
theorem Efficient.exists_uniform {S : Strategy} (h : S.Efficient) :
    ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins := by
  obtain ⟨A, hA, hc, -⟩ := h
  exact ⟨A, hA, hc⟩

/-- A strategy reads at most an `m(|x|)`-bit prefix of each received message [PS10, §4.4, time
complexity: an interactive machine of time complexity `t(|x|)` reads at most `t(|x|)` cells of
its communication tape per activation, "independently of the content of the messages it
receives"] (Def-116.b, the message half of the text's bound in `|x|`): the next-message
function is unchanged when every received message is truncated to its first `m.eval |x|` bits.
Together with `Efficient` this is the text's PPT interactive machine — the activation is
computed in time polynomial in `|x| + |z| + rounds · m(|x|)` by truncating the messages first —
whereas `Efficient` alone is polynomial in the total message length (D8).

**Repair (run-3 audit P9-1):** added; the class `IP` requires it of the verifier. -/
def ReadsPrefix (S : Strategy) (m : PolyExpr) : Prop :=
  ∀ x z r hist, S.next x z r hist = S.next x z r (hist.map (List.take (m.eval x.length)))

/-- Under a message-prefix cap the next message depends only on the truncated history. -/
theorem ReadsPrefix.next_congr {S : Strategy} {m : PolyExpr} (h : S.ReadsPrefix m)
    {x z r : List Bool} {hist hist' : List (List Bool)}
    (he : hist.map (List.take (m.eval x.length)) = hist'.map (List.take (m.eval x.length))) :
    S.next x z r hist = S.next x z r hist' := by
  rw [h x z r hist, h x z r hist', he]

/-- The message-prefix cap is monotone: a cap `m` implies every pointwise larger cap `m'`
(`List.take_take`: truncating to `m'(|x|)` and then to `m(|x|) ≤ m'(|x|)` bits is truncating to
`m(|x|)` bits). -/
theorem ReadsPrefix.mono {S : Strategy} {m m' : PolyExpr} (h : S.ReadsPrefix m)
    (hle : ∀ n, m.eval n ≤ m'.eval n) : S.ReadsPrefix m' := by
  intro x z r hist
  refine h.next_congr ?_
  rw [List.map_map]
  refine List.map_congr_left fun msg _ => ?_
  simp only [Function.comp_apply, List.take_take, min_eq_left (hle _)]

end Strategy

/-! ### Executions -/

/-- Which party moves at move `k` (0-indexed): the verifier moves at the even positions when
it moves first, at the odd ones otherwise. -/
def moverIsV (vFirst : Bool) (k : ℕ) : Bool :=
  if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)

/-- With the verifier first, it moves at the even positions. -/
@[simp] theorem moverIsV_true (k : ℕ) : moverIsV true k = decide (k % 2 = 0) := rfl

/-- With the prover first, the verifier moves at the odd positions. -/
@[simp] theorem moverIsV_false (k : ℕ) : moverIsV false k = decide (k % 2 = 1) := rfl

/-- The messages received by `P` and by `V` after `k` moves of the execution
`P_{rP}(x, zP) ↔ V_{rV}(x, zV)` [PS10, §4.4, the execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)`]
(Def-115.a): at move `k` the active party applies its next-message function to the messages
it has received so far and the message is appended to the other party's received list. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 =>
    let e := exec P V vFirst x zP zV rP rV k
    if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
    else (e.1, e.2 ++ [P.next x zP rP e.1])

/-- Before the first move nothing has been received. -/
@[simp] theorem exec_zero (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    exec P V vFirst x zP zV rP rV 0 = ([], []) := rfl

/-- One more move: the active party's message is appended to the other party's list. -/
theorem exec_succ (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vFirst x zP zV rP rV (k + 1) =
      (let e := exec P V vFirst x zP zV rP rV k
       if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
       else (e.1, e.2 ++ [P.next x zP rP e.1])) := rfl

/-- After `k` moves exactly `k` messages have been sent in total. -/
theorem exec_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    (exec P V vFirst x zP zV rP rV k).1.length + (exec P V vFirst x zP zV rP rV k).2.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [exec_succ]
    split_ifs <;> simp only [List.length_append, List.length_singleton] <;> omega

/-! ### Views -/

/-- A party's view [PS10, §4.4] (Def-115.b): the common input, its auxiliary input, its random
tape and the messages it received. -/
structure View where
  /-- The common input. -/
  x : List Bool
  /-- The party's auxiliary input. -/
  z : List Bool
  /-- The party's random tape. -/
  r : List Bool
  /-- The messages the party received, in order. -/
  received : List (List Bool)

/-- The string encoding of a view, `⟨⟨x, z⟩, ⟨r, messages⟩⟩` (the sample handed to
distinguishers and produced by simulators in the zero-knowledge definitions). -/
def View.encode (v : View) : List Bool :=
  pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))

/-- The output of a party on a view [PS10, §4.4, `out(v)`] (Def-115.d): its next-message
function on the complete history. -/
def Strategy.out (S : Strategy) (v : View) : List Bool := S.next v.x v.z v.r v.received

/-- The output on a view is the next-message function on the view's complete history:
`S.out v = S.next v.x v.z v.r v.received`. -/
theorem Strategy.out_eq (S : Strategy) (v : View) : S.out v = S.next v.x v.z v.r v.received :=
  rfl

/-! ### Protocols -/

/-- A protocol [PS10, §4.4] (Def-114.b): a prover strategy, a verifier strategy, the number of
messages exchanged (an explicit polynomial in `|x|`) and the first mover (`true` = verifier
first, as in the graph non-isomorphism protocol; `false` = prover first, as in the graph
isomorphism and 3-colouring protocols). The verifier's verdict is its next-message function
on the complete history.

**Deviation (D8):** fixed number of messages `rounds.eval |x|`; a halting party sends `[]`.
If the verifier is the last mover (prover first with an even number of messages, or verifier
first with an odd number), its last message coincides with its verdict — both are `V.next` on
the same history (`outV_eq_getLast_of_moverIsV`) — so a verifier whose final message differs
from its verdict is not expressible; protocols are therefore stated so that the prover moves
last, or the verifier's last message is read as the verdict (the `n`-fold protocols)
(run-3 audit P9-3). -/
structure Protocol where
  /-- The prover's strategy. -/
  P : Strategy
  /-- The verifier's strategy. -/
  V : Strategy
  /-- The number of messages exchanged, as a polynomial in `|x|`. -/
  rounds : PolyExpr
  /-- Whether the verifier sends the first message. -/
  verifierFirst : Bool

namespace Protocol

/-- The joint coin space of an execution of `π` with the prover strategy `P'` on `x`: the
prover's and the verifier's random tapes at parameter `|x|` [PS10, §4.4, random executions]
(Def-116.a). -/
abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
  P'.Coins x.length × π.V.Coins x.length

/-- The protocol with the verifier replaced by `V'` (the cheating verifier `V*` of the
zero-knowledge definitions), same prover, round count and first mover. -/
def withV (π : Protocol) (V' : Strategy) : Protocol := { π with V := V' }

/-- The verifier of `π.withV V'` is `V'`. -/
@[simp] theorem withV_V (π : Protocol) (V' : Strategy) : (π.withV V').V = V' := rfl

/-- The prover of `π.withV V'` is the prover of `π`. -/
@[simp] theorem withV_P (π : Protocol) (V' : Strategy) : (π.withV V').P = π.P := rfl

/-- The round count of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_rounds (π : Protocol) (V' : Strategy) : (π.withV V').rounds = π.rounds := rfl

/-- The first mover of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_verifierFirst (π : Protocol) (V' : Strategy) :
    (π.withV V').verifierFirst = π.verifierFirst := rfl

/-- Replacing the verifier by itself changes nothing. -/
@[simp] theorem withV_self (π : Protocol) : π.withV π.V = π := by
  cases π
  rfl

/-- The transcript (messages received by `P'`, messages received by `V`) of the execution
`P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` with all `rounds.eval |x|` moves [PS10, §4.4] (Def-115.c). -/
def transcriptWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
    List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)

/-- The transcript against `P'` is `exec` with all `rounds.eval |x|` moves, on the encoded tapes:
`π.transcriptWith P' x y z r =
exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)`. -/
theorem transcriptWith_eq (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) :
    π.transcriptWith P' x y z r =
      exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length) :=
  rfl

/-- The transcript of the honest execution `P(x, y) ↔ V(x, z)` (Def-115.c). -/
def transcript (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    List (List Bool) × List (List Bool) :=
  π.transcriptWith π.P x y z r

/-- The honest transcript is the transcript against the honest prover:
`π.transcript x y z r = π.transcriptWith π.P x y z r`. -/
theorem transcript_eq_transcriptWith (π : Protocol) (x y z : List Bool)
    (r : π.ExecCoins π.P x) : π.transcript x y z r = π.transcriptWith π.P x y z r :=
  rfl

/-- The verifier's output in `P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `out_V`] (Def-115.d):
`V.next` on the complete history.

**Deviation (D8, run-3 audit P9-3):** when the verifier is the last mover this is also the
last message it sent (`outV_eq_getLast_of_moverIsV`); see `Protocol`. -/
def outV (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : List Bool :=
  π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2

/-- The verifier's output against `P'` is `V.next` on the messages it received:
`π.outV P' x y z r = π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2`. -/
theorem outV_eq (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
    π.outV P' x y z r = π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2 :=
  rfl

/-- The honest prover's output in `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` (Def-115.d). -/
def outP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : List Bool :=
  π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1

/-- The honest prover's output is `P.next` on the messages it received:
`π.outP x y z r = π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1`. -/
theorem outP_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outP x y z r = π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1 :=
  rfl

/-- The honest verifier's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_V`]
(Def-115.b). -/
def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩

/-- The honest verifier's view consists of `x`, its auxiliary input `z`, its tape and the
messages it received: `π.viewV x y z r = ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩`.
-/
theorem viewV_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.viewV x y z r = ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩ :=
  rfl

/-- The honest prover's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_P`]
(Def-115.b). -/
def viewP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩

/-- The honest prover's view consists of `x`, its auxiliary input `y`, its tape and the
messages it received: `π.viewP x y z r = ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩`.
-/
theorem viewP_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.viewP x y z r = ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩ :=
  rfl

/-- The execution `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` as the pair of views (the joint view)
[PS10, §4.4] (Def-115.a). -/
def execution (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View × View :=
  (π.viewP x y z r, π.viewV x y z r)

/-- The verifier's output is its output function on its view (Def-115.d). -/
theorem outV_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outV π.P x y z r = π.V.out (π.viewV x y z r) := rfl

/-- The prover's output is its output function on its view (Def-115.d). -/
theorem outP_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outP x y z r = π.P.out (π.viewP x y z r) := rfl

/-- The transcript is the pair of received-message components of the two views. -/
theorem transcript_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.transcript x y z r = ((π.viewP x y z r).received, (π.viewV x y z r).received) := rfl

/-- The verifier's output against `P'` only depends on `P'` through the transcript. -/
theorem outV_withV (π : Protocol) (V' P' : Strategy) (x y z : List Bool)
    (r : (π.withV V').ExecCoins P' x) :
    (π.withV V').outV P' x y z r =
      V'.next x z (List.ofFn r.2)
        (exec P' V' π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
          (π.rounds.eval x.length)).2 := rfl

/-- The verdict convention of D8 made explicit (run-3 audit P9-3): if the verifier makes the
last of the `k + 1` moves (`moverIsV verifierFirst k`), the last message it sent — the last
message `P'` received — is its verdict, because both are `V.next` on the messages `V` received
in the first `k` moves (`exec_succ`, `List.getLast?_concat`). -/
theorem outV_eq_getLast_of_moverIsV (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) {k : ℕ} (hk : π.rounds.eval x.length = k + 1)
    (hV : moverIsV π.verifierFirst k = true) :
    (π.transcriptWith P' x y z r).1.getLast? = some (π.outV P' x y z r) := by
  unfold outV transcriptWith
  rw [hk, exec_succ]
  simp [hV]

/-! ### Random executions -/

/-- A random execution is a sampler on the product of the two coin spaces [PS10, §4.4]
(Def-116.a): the probability of any event of the verifier's output is the average over the
prover's coins of its conditional probability over the verifier's coins (`uprob_prod`). -/
theorem uprob_outV_eq_uexp (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) =
      uexp (fun r₁ : P'.Coins x.length =>
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))) :=
  uprob_prod _

/-- A cheating prover may be taken deterministic: for every event of the verifier's output
there is a fixed prover random tape under which the event is at least as likely as on average
(the "without loss of generality `P*` is deterministic" remark behind the soundness clause of
[PS10, Definition 116.1]). -/
theorem exists_proverCoins_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    ∃ r₁ : P'.Coins x.length,
      uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) ≤
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂))) := by
  rw [uprob_outV_eq_uexp]
  set f : P'.Coins x.length → ℝ :=
    fun r₁ => uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))
  have hcard : (0 : ℝ) < Fintype.card (P'.Coins x.length) := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∑ _a : P'.Coins x.length, uexp f ≤ ∑ a, f a := by
    rw [sum_const, card_univ, nsmul_eq_mul, uexp, mul_div_cancel₀ _ hcard.ne']
  obtain ⟨a, -, ha⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨a, ha⟩

end Protocol

end TCSlib.Cryptography

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== design/S2b-efficiency.md =====

# S2b design note: the efficiency of reductions (the machine layer's crux)

Status: **route identified, 2026-11-04; nothing written yet.**

## The statement needed

Every reduction in prongs A–D has the same shape. Given a machine adversary `A` against the
oracles `spec`, the reduction answers `A`'s queries with an implementation `impl : QueryImpl spec σ
spec'` that may query its own oracles `spec'` and draw coins. The composite must be a machine
adversary against `spec'`, so that the hardness assumption (a PRF, a OWF, a TDP, …), which
quantifies over machines, applies to it. Informally:

> If `impl`'s work per query is a polynomial-time function of encoded strings, and `A` makes at
> most `q(n)` queries, then there are a machine `B` and a codec for `spec'` such that, for every
> `n` and coin string, `B.toComp codec' n q'(n) r'` equals the simulation of
> `A.toComp codec n q(n) r` by `impl` (outputs only), with `q'(n) = q(n) · (per-query cost)` and
> the coins `r'` split into `A`'s and `impl`'s.

Proved once, it spares every reduction of prongs A–D a machine construction of its own. The ch. 2–4
layer built one per reduction (`Asymptotic/GGMReduction*`, `HardCoreGL*`, …), each several hundred
lines.

## A close relative (found 2026-11-05)

Frederick's GGM reduction machine (`TCSlib/Cryptography/Asymptotic/GGMReduction.lean`, `GGMReductionEval.lean`) is this construction for one particular handler:
- it runs a next-query machine to completion in a state loop, holding the encoded history and a lazily sampled table, and each round runs the machine, decodes the move and answers from the reduction's own coins;
- its loop, `GGMRed.stateLoopFun` with `stateLoopFun_poly` and `stateLoopFun_eval`, is generic in start, step, acceptance and output, and **is reused verbatim**;
- the round, `rawFun_poly` and the GGM identity are specific, and are generalized by analogy.

The fill (ruled 2026-11-05: Claude, after gate 02) adds the **log-replay variant** for reductions that are oracle machines: each round reads the answers to the handler's own queries from the reduction's log, and stops at the first unanswered one. GGM becomes an instance at the integration of ch. 2–4 (coordination point F-4).

## Relation to P^O = P (checked 2026-11-05, at the user's prompt)

In substance the efficiency result is *FP with an efficiently implementable oracle is FP*. `main` (and the ch. 3–4 branch) prove the Turing-machine form: `Turing.FinOracleTM.exists_plain_simulation` (`Complexity/TuringMachine/Build/OracleSim.lean`), behind `Complexity.POracle_eq_P_of_mem_P` (`ClassOracle/Classes.lean`). It is **not reused**, for three reasons:
1. **The machine model.** It is about oracle Turing machines ([AB09, Def 3.4]: query tape, `qQuery`/`qYes`/`qNo`). The ch. 2–4 adversaries are plain machines restarted on the encoded history (D7). In that model the statement is function-level, closure of polynomial-time functions under polynomially bounded iteration (`Complexity.polyTimeComputable_iterate`/`iterateFind`, `Randomized/Repetition.lean`), and the tape engineering of `OracleSim` has no counterpart.
2. **The oracles.** It needs a *language* oracle decided by a plain machine (one-bit answers, no state, no coins). Ours answer strings and are stateful and randomized; using it would need bitwise answer encodings and an encoding of state and coins.
3. **Availability.** `OracleSim` and `ClassOracle` are on `main` and the ch. 3–4 branch, not on `cryptography/pass-shelat-ch2-4` until `main` is merged in.

Routing through it would mean a new bridge from NUPPT next-move machines to oracle TMs, which costs more than the function-level route. There, polynomial time is already generic (`GGMRed.stateLoopFun_poly`), and the remaining work is the functional equation, of which `GGMReductionEval.lean` is the worked example.

## The route

1. **Handlers as string functions.** A `PolyHandler` packages `impl` as polynomial-time maps on
   encodings:
   - `step : ⟨state, query⟩ ↦` either "ask `spec'` this query, with this intermediate state", or
     "answer the adversary with this, and this new state";
   - the per-query number of target queries bounded by a constant `c` (or a polynomial).

   Coins are drawn from a segment of `B`'s tape, by Frederick's `exists_split` (`Closure.lean`).
2. **The replay step.** `B`'s next-move function, on its own encoded log, recomputes the whole
   simulated interaction. Starting from the empty log of `A` and the initial state, it repeats:
   - run `A`'s next-move function (`A.output`, polynomial-time by
     `NUPPT.polyTimeComputable_output`);
   - feed `A`'s query to the handler's `step`;
   - read the answers to the handler's target queries from `B`'s log.

   It ends when it reaches a target query not yet answered (`B`'s next move) or `A`'s final
   output (`B`'s output). Each round is a polynomial-time function of a state word of polynomial
   size.
3. **Iteration.** The replay is a polynomial number of rounds (at most `q(n)·(c + 1)`). The library
   has `Complexity.polyTimeComputable_iterate` (`Complexity/Randomized/Repetition.lean`):
   iterating a polynomial-time step `R(|x|)` times, with the orbit's lengths bounded by `P(|x|)`,
   is polynomial-time. The replay's number of rounds is a polynomial in `n`, and `1^n` is part
   of the input, so `R(|x|)` dominates it.
4. **The machine.** `NUPPT.ofPolyTime` of the replay function, with `A`'s advice and coin
   polynomial combined with the handler's (`exists_seq`/`exists_split`), is `B`.
5. **The functional equation.** `B.toComp codec' n q' r'` equals the simulation. The proof is by
   induction on `A`'s budget, matching `buildComp`'s unfolding against `simulate`'s. This part
   is pure framework reasoning on top of the decoder lemmas (`buildComp`, `toComp_singleCodec`'s
   pattern).

## Obligations and size (estimate)

| Piece | Kind | Lines |
|---|---|---|
| `PolyHandler` and its semantics as a `QueryImpl` | definitions, small lemmas | 150–250 |
| the replay step and its polynomial-time computability (pairing calculus, `polyTimeComputable_ite`, length bounds) | FP-level | 300–600 |
| the orbit length bound | arithmetic | 100–200 |
| the functional equation | framework | 200–400 |
| the headline lemma | glue | 50–100 |

The total estimate is 0.8–1.5k lines. The FP-level part reuses Frederick's pairing calculus and
his `Repetition` and `StateLoop` toolkit. It cites them only through published statements, since
under rule 10 his definitions are not unfolded.

## Who and when

- It depends only on the S2a core (gate 02) and the B3 decoder.
- It is a natural **fill item** (D-7: Claude), dispatched once gate 02 closes, with a brief built
  on this note. Alternatively the maintainer writes it.
- **Pre-ship probe** for the brief: instantiate `polyTimeComputable_iterate` on a toy replay
  (a handler answering every query with a fixed function), so that the brief's route is checked
  in Lean before dispatch.
