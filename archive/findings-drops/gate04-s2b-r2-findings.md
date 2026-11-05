# Gate 04 — S2b round 2 external audit findings

**Verdict: DO NOT CLOSE.**  
**0 blockers, 1 major, 2 minors.**

The codec repair is adequate. The restated efficiency targets address the input, finalization, exact-output and PRF-interface deficiencies identified as N1. F02 remains open: one newly published equation is proved by reducing definitions from another file, contrary to the submitted publication policy. The four explicitly deferred efficiency proofs are not findings merely because they contain `sorry`.

**Audited head:** `243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`, PR #195.  
**Round 1 head:** `afe5982f612081bba2fbcec9ab41adcbbc118b13`.  
**Bundle:** 32 sections; SHA-256 `82bf3e91be5d8d49879383f7a928fc124e261d91f53453765cf0cdc341f70239`. No expected round 2 bundle digest was supplied.  
**Source PDF:** Pass–shelat, third edition, January 2010; SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Book page = PDF page − 12.

All 25 supplied Lean files have Git blob hashes matching the pinned head. The repair diff reverse-applies cleanly to those files. The embedded round 1 findings, excluding bundle separators, match the digest in `resolutions-r1.md`.

Paths below are relative to `TCSlib/Cryptography/` unless otherwise stated. Line numbers refer to individual extracted files.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-01 | **Major** | `Games/Simulate.lean:132–134` · `QueryImpl.passthrough_apply`; `resolutions-r1.md` · F02 | The repair satisfies the publication/no-unfolding requirement. | The new proof is `rfl`. Reducing the locally defined `passthrough` and `ofComp` leaves `(OracleComp.call i x).bind (fun y => .pure (y, s))`. Identifying this with the stated query constructor requires reducing `OracleComp.call` and `OracleComp.bind`, both defined in `Games/OracleComp.lean`. They are TCSlib definitions, not abbreviations or core/Mathlib definitions covered by the policy exception. The equation is mathematically correct; its proof still crosses the prohibited implementation boundary. | Prove it through `ofComp_apply` and `OracleComp.call_bind`, as below. Include new equation proofs, not just re-pointed old consumers, in the seal coverage. F02 remains unresolved until this is repaired or explicitly accepted as debt. |
| R2-02 | Minor | `briefs/pass-shelat-ch5-8/gates/04-s2b/pack-r2.md:47–58`; `resolutions-r1.md` · F05, N2, N4, N7 | The regenerated execution and seal evidence is supplied in `evidence-r2/`, and the supporting records establish the staging resolutions. | The bundle contains only `evidence-r2/repair.diff.txt` and `evidence-r2/changed-files.txt`. It omits `replay.log`, `axioms.log`, `lint.log`, `check8.log`, and `seal.py.txt`/its results. The maintainer review defining N1–N7 and the referenced updated duplication ledger are also absent. The pinned repository's duplication ledger ends at DL-7, so it does not verify the claimed DL-9-onward pointer. Source inspection confirms 379 public theorems and four direct admissions, but cannot establish the claimed transitive axiom sets or successful executions. | Attach the named logs, seal script and results with head/module/definition coverage. Supply the review and updated ledger reference, or describe those records as scheduled rather than already supplied. Keep source counts distinct from kernel/axiom verification. |
| R2-03 | Minor | `Games/Efficiency.lean:330–333,392–394,451–454` · `InteractiveHandler`, `call`, `finish` docstrings | A spent/exhausted query budget produces the all-false result. | With `outLen = 1`, `finCall = 0`, and `finRun` constantly returning `pairEncode [true] [true]`, `finish` returns the true bit. `buildComp_zero_of_ret` permits a return at zero remaining budget. Only another **query** at zero remaining budget invokes the timeout. The same distinction applies to `call`. | Say “a malformed move, or a further query after the query budget has been spent, returns the all-false result.” Retain the corrected activation bounds. No definition or theorem statement needs changing. |

R2-01 retains F02's major classification because the claimed resolution of the explicit publication requirement is incomplete. It is not an allegation of a false theorem or an additional admission.

The proposed R2-01 proof is:

```lean
by
  rw [passthrough, ofComp_apply, OracleComp.call_bind]
```

This is a source-level proposed repair, not a compiled patch. No fresh Lean seal failure or successful repair compilation is claimed.

## Resolution of every round 1 item

F01: **fixed** — `decodeIdx` now accepts exactly the bounded all-true unary words; the query converse, return round trip and noncanonical-default theorem determine the move decoder on every word.

F02: **not resolved** — the missing equations and identified bridge consumers are substantially repaired, but the new `passthrough_apply` proof still reduces foreign definitions; see R2-01. The supplied material also does not establish the reported seal execution.

F03: **fixed** — `PolyHandler.answer` explicitly documents independent component defaults, and its two parsing-case lemmas expose them exactly.

F04: **fixed** — the contract now distinguishes at most `perCall(n)` outer queries from at most `perCall(n) + 1` handler activations. R2-03 concerns the separate timeout wording, not this corrected bound.

F05: **fixed, for the accounting defect** — the resolution corrects the round 1 public/private scope and counts. Independently, the new files contain 394 explicit theorem declarations: 379 public and 15 private, including the new private decoding helper. Exactly four direct `sorry` occurrences occur in these files. The claimed 375 standard transitive axiom sets remain an execution attestation, not independently verified evidence; see R2-02.

F06: **fixed** — the query-count description now promises an upper bound; the history lemma describes its query projection; the decryption premise describes projected lengths; the query-chain statement describes evaluation equality; the block duplicate is described as public; and both `tableDist` and `ggmDist` cost descriptions state the adversary-bound condition.

N1: **fixed at the contract level** — input construction, exact final output, oracle-using finalization, the input-free companion and the singleton PRF bridge are now expressible. The eight intended uses are assessed below. The four proofs and downstream applications remain declared fill/integration work.

N2: **not resolved in the supplied evidence** — check 8 and seal results are asserted but not attached. This does not establish that those checks failed; see R2-02.

N3: **recorded** — the inaccurate promise of traced/probabilistic results “in a later part of this file” remains at `Bridges/Strategies.lean:49–50`, but the resolution explicitly schedules its correction at integration. No such results are certified here.

N4: **recorded as scheduled debt** — the public duplicate is accurately identified and its cleanup destination is explicit in the resolution. This accepts the recorded cleanup commitment, not the unverified assertion that the cited DL-9-onward ledger update has already been integrated; see R2-02.

N5: **fixed** — `Party.endWithT_ne_outOfFuel` uses `Option.elim_none` and `Option.elim_some` instead of passing `Option.elim` to `simp`.

N6: **fixed** — noninteractive componentwise defaulting and interactive joint defaulting are now distinguished correctly.

N7: **not resolved in the supplied evidence** — the claimed staging check is not supplied, as for N2.

The N-items are assessed against their descriptions in `resolutions-r1.md`; the full maintainer review was not supplied.

## Body-first definition and statement assessment

The changed codec and efficiency definitions were first inspected with comments removed. These are the resulting restatements, subsequently compared with their docstrings.

| Definition or structure | Behavior read from its body | Documentation assessment |
|---|---|---|
| `decodeIdx` | Accept a word exactly when its length is below `k` and every bit is true; return its length as the index. | Matches. This deliberately changes malformed-index behavior. |
| `encodeBitMove` | Encode a query using the false tag, unary oracle index and exact query bits; encode a return using the true tag and exact output bits. | Matches; both constructor equations are present. |
| `bitSpecAt` | Substitute the parameter into each query/answer length polynomial. | Matches; the new equation exposes precisely this substitution. |
| `seedIn` | Pair the unary parameter with the pair of reduction input and seed. | Matches. Pairing is self-delimiting, including empty components. |
| `PolyHandler` | Supply polynomial state/seed lengths, an arbitrary initial-state family, and three deterministic polynomial-time word functions: input construction, query answering, final output. | Matches the nonuniform contract. `init` is not required to be computable; it can be put in polynomial-length advice. |
| `PolyHandler.input` | Encode parameter, reduction input, seed, current state, oracle index and query. | Body unchanged; the new equation matches exactly. |
| `PolyHandler.advInput` | Apply `advIn` to the encoded parameter/input/seed context. | Matches. Its output is not artificially truncated or decoded. |
| `PolyHandler.result` | Apply `out` to the context paired with terminal state and adversary output. | Matches. The result is an arbitrary word, not a Boolean verdict or a fixed-width projection. |
| `PolyHandler.answer` | Run the answer function, parse a pair, and decode answer/state separately; a bad pair zeros both, while a bad component zeros only itself. | Matches the repaired prose and complete parsing cases. |
| `PolyHandler.impl` | Return that answer/state pair purely, with no ambient sampling or oracle query. | Matches; the seed is already fixed. |
| `InteractiveHandler` | Add an outer oracle family, a per-inner-query outer budget, a polynomial output length, a finalization budget, and separate polynomial next-move functions for servicing queries and finalization. | Fields and intended stages match. The timeout sentence needs R2-03. |
| `InteractiveHandler.input` | Encode the query context plus the outer log for this call. | Body unchanged; the new equation matches. |
| `InteractiveHandler.advInput` | Compute the adversary's input from parameter, reduction input and seed. | Matches. This stage itself makes no outer queries. |
| `InteractiveHandler.call` | Start a bounded outer computation with an empty local log; return a word containing the answer followed by the new state. Malformed moves and attempted over-budget queries return all zeros. | Matches apart from R2-03. A return is still inspected and accepted at zero remaining budget. |
| `InteractiveHandler.impl` | Execute one call and split its result at the prescribed answer length. | Matches. The split uses exactly `dout i` bits for the answer and `stateLen` for state. |
| `InteractiveHandler.finInput` | Encode context, terminal state, adversary output and this finalization's outer log. | Matches. It does not silently include earlier calls' logs. Information needed later must be retained in state. |
| `InteractiveHandler.finish` | Start a fresh outer computation with budget `finCall`, decode returns at `outLen`, and use the all-false timeout. | Matches apart from R2-03. This stage executes even when the inner query budget is zero. |

The remaining repaired files add equations, change proof bodies, or narrow descriptions; they do not change the corresponding definition bodies. The handler structures intentionally acquire new required fields under R-04-3.

| Target | Actual quantified conclusion | Docstring/contract assessment |
|---|---|---|
| T1 · `exists_handlerMachine` | One machine works for every parameter and every input. For each parameter, a single coin equivalence works for all inputs/seeds/adversary tapes. The pure simulation returns some definite output/state pair, and the machine's **entire output word** equals `H.result` on that pair. | Matches. Equality to `pure (a,s)` fixes the pair; the existential witnesses cannot be unrelated to the execution. |
| T2 · `exists_interactiveHandlerMachine` | The simulated inner computation, bound to finalization on its terminal state/output, equals the outer machine's computation tree at budget `q(n) * perCall(n) + finCall(n)`. | Matches. This is tree equality, stronger than equality against a particular oracle or equality of acceptance probabilities. The finalizer receives `res.2` as state and `res.1` as adversary output, in the correct order. |
| `exists_toCompOn_of_toComp` | One machine with the same coin polynomial ignores every supplied input and realizes the original input-free computation for every codec and budget. | Matches. The machine and coin equivalence are chosen before the codec, input and budget; this is not a separate machine chosen for each execution. |
| T4 · `exists_toOracleAdversary_of_bitCodec` | A machine against one fixed-width bit oracle, with one-bit output and empty auxiliary input, has an equal-coins old-style next-query machine with the same evaluated Boolean result, for every budget and deterministic oracle. | Matches its stated scope. It does not assert tree equality, support multiple outer oracles, or directly preserve an arbitrary auxiliary input. Those stronger conclusions are not needed for the listed PRF applications. |

All four remain `sorry`. These assessments establish that the statements express usable obligations and that no counterexample was found; they do not supply their missing Lean proofs.

## Codec completeness

For every word `iw` and `i : Fin k`, the repaired condition gives

\[
\operatorname{decodeIdx}(k,iw)=\operatorname{some}(i)
\iff iw=\operatorname{List.replicate}(i,\mathrm{true}).
\]

Forward: the successful branch gives an all-true word of length equal to the returned index; equality of the returned `Fin` values identifies that length with `i`. Reverse: the replicated word has length `i < k`, so the successful branch returns `i`. The `none` converse follows by splitting the `Option` result.

For a full move word, the possibilities are exhaustive:

1. It is the canonical encoding of a query: `decodeBitMove_eq_query_iff` identifies both its oracle and payload.
2. It is the canonical encoding of a return: `decodeBitMove_ret` identifies the returned bit vector.
3. It is neither: `decodeBitMove_of_not_canonical` identifies the all-false return.

The pairing converse and fixed-length decoding converse justify recovery of the original word in the successful branches. Query and return tags are distinct. `decodeBitMove_encodeBitMove` is a left inverse, so `encodeBitMove_injective` follows. No converse claiming that *only* a canonical return can decode to the default is asserted; that would be false because malformed words intentionally share the default.

The round 1 witness now satisfies `decodeIdx 2 [false] = none`. At `k = 0` no query is possible. Zero-length query and output types remain inhabited by their unique empty bit vectors; no argument requires a positive length.

## Equation coverage and repaired consumers

The diff adds 99 public theorems: 97 equations, case lemmas or codec consequences, and the two new admitted companion/T4 targets. It also adds one private fixed-length-decoding helper. The 97 public lemmas were checked by the following complete grouping; the original 91 are augmented by six equations for R-04-3.

| File | Added public equation/case/consequence surface | Assessment |
|---|---|---|
| `Asymptotic/PRF` · 7 | `encodeHist_nil/cons`; all four `buildTree_zero/succ_of_ret/query` cases; `toOracleAdversary_eq`. | Exact encoding and exhaustive budget/move equations. Returning at budget zero is preserved. |
| `Games/Advantage` · 3 | `accept_eq`, `advantage_eq`, `guessGame_eq`. | Exact probability expression, absolute gap and sampling/bind order. |
| `Games/BitCodec` · 16 | `bitSpec_dom/rng`; both index converses; `zeroBits_apply`, `ofFn_zeroBits`; both encoder cases; all three codec projections; `encodeLog_bitCodec`; query converse; noncanonical default; round trip; injectivity. | Correct. The converse/default family supplies complete decoder coverage; the other consequences are correctly described as consequences, not falsely advertised as defining equations. |
| `Bridges/Experiments` · 1 | `acceptGame_eq`. | Exact sampling order and returned event. |
| `Bridges/Machines` · 6 | Three `singleCodec` projections; `toHist_nil/cons/append_singleton`. | Exact projections and complete list recursion. The append lemma is a correct derived equation. |
| `Bridges/QueryTree` · 3 | `evalFn_pure/query`, `treeImpl_apply`. | Exact deterministic evaluation and normalized one-query implementation. `treeImpl_apply` uses published bind/call equations. |
| `Bridges/Strategies` · 6 | `turnParty_zero`; all three waiting cases; `alt_zero/succ`. | Exact cases, including the off-schedule defaults. The pre-existing `turnParty_succ` completes the turn cases. |
| `Games/Efficiency` · 15 | `bitSpecAt_eq`, `seedIn_eq`; noninteractive `input_eq`, `advInput_eq`, `result_eq`, both answer parsing cases, `answer_of_run_eq`, `impl_apply`; interactive `input_eq`, `advInput_eq`, `call_eq`, `impl_apply`, `finInput_eq`, `finish_eq`. | Exact. The answer parsing cases cover all runs; `answer_of_run_eq` is a useful specialization. Both builder equations expose the empty local log, exact widths and budgets. |
| `Games/Machines` · 8 | `encodeLog_nil/cons`; four builder cases; `toComp_eq`, `toCompOn_eq`. | Exact. `toCompOn` pairs auxiliary input with the encoded log; `toComp` does not. |
| `Games/OracleComp` · 4 | `singleSpec_dom/rng`, `allOutputs_pure/query`. | Exact projections and predicate cases. |
| `Games/Protocols` · 10 | Three `ExecOutcome.swap` cases; three `step` cases; three `close` cases; `endWith_eq`. | Exact constructor coverage, including coin queries and a send after termination. |
| `Games/Simulate` · 6 | `ofComp_apply`, `passthrough_apply`, `sum_inl/inr`, `comp_apply`, `withLog_apply`. | All statements are correct. `passthrough_apply` has the proof-policy defect R2-01. |
| `Pseudorandom/Functions/OracleAdversary` · 5 | `induct_ret/query`, `simulate_ret/query`, `oracleDist_apply`. | Exact recursor, query translation and evaluation equations. |
| `ZeroKnowledge/Interaction` · 7 | `Strategy.out_eq`; `transcriptWith_eq`, `transcript_eq_transcriptWith`, `outV_eq`, `outP_eq`, `viewV_eq`, `viewP_eq`. | Exact fields and tape/history order; D8's scheduling/output convention is unchanged. |

The re-pointed old proofs inspected in the repair diff use the appropriate public interfaces: the history/builder/machine bridge uses encoding and builder equations; the query-tree bridge uses simulation/evaluation/bind equations; B4 uses executor, waiting, alternation and D8 equations; the experiment bridge uses `accept_eq`/`advantage_eq`; and the changed `Hopping`/trace proofs use `simulate_pure` and `allOutputs_pure/query`. No remaining foreign-definition read was found in those re-pointed steps. R2-01 is in a **new equation proof**, so a seal limited to old re-pointed consumers would not establish its compliance.

This is not a fresh certification of every unchanged legacy proof in the 25 files. For example, unchanged S2a consumers are not silently declared to satisfy a broader seal than the pack reports.

## Efficiency, budgets and non-vacuity

No missing hypothesis was found for the stated nonuniform, fixed-width, one-adversary-execution scope:

- `advIn_poly`, `poly`, `out_poly` and `finRun_poly` constrain actual word functions, rather than assuming the desired reduction is already a machine.
- For arbitrary `z`, the working length is polynomial in `n + length(z)`. This is compatible with the pinned `NUPPT` definition, whose polynomial time is measured in its encoded input length. Cryptographic applications separately supply polynomial-length challenges/advice.
- The arbitrary initial state has exactly `stateLen(n)` bits and can be included in nonuniform advice. A uniform-machine conclusion would require an additional restriction, but neither T1 nor T2 asserts one.
- Bit-vector state, seed, query, answer and output types are nonempty even at length zero. Constant handlers and constant-output adversaries give inhabited examples. Pure noninteractive implementations cannot get stuck on an empty answer type.
- The equivalence of coin spaces is independent of `z` and preserves uniform counting measure. No extra probabilistic assumption about that equivalence is needed.

For T2, let an execution make `m` inner queries, with `m ≤ q(n)`. Each call makes at most `perCall(n)` outer queries, and finalization makes at most `finCall(n)`. Thus

\[
\#\text{outer queries}
\le m\,\mathrm{perCall}(n)+\mathrm{finCall}(n)
\le q(n)\,\mathrm{perCall}(n)+\mathrm{finCall}(n).
\]

For the direct simulation, and within one complete replay pass, the activation bounds are `q(n) + 1` for the inner next-move function, at most `m * (perCall(n) + 1)` for query handlers, and at most `finCall(n) + 1` for the finalizer. The compiled next-move machine can repeat this work on successive outer activations; their number is also polynomial. Calls that make no outer query still require computation, but their number is bounded by the inner budget. Thus zero-query-cost handlers do not create an unbounded replay.

Because pairing has length `2 * length(first) + 2 + length(second)`, one canonical log entry for oracle `i` has length `2i + 2 din(i) + dout(i) + 4`. Its contribution to the nested log is `4i + 4 din(i) + 2 dout(i) + 10`. The oracle family is fixed and finite, all widths and budgets are polynomial, and histories therefore have polynomial size. This supports the intended bounded replay construction, without proving that construction in Lean.

The input-free companion does not need efficient arbitrary codecs: it merely projects `pairEncode x log` to `log`, independent of the codec. The pinned `NUPPT.exists_comp` has exactly the required pre/post-processing contract.

For T4, insert the sole index word `[]` into each old history entry and pair the resulting log with the empty auxiliary input. Translate a decoded new query to `pairEncode [false] x`, and a decoded one-bit return to `[true, b]`. Malformed new moves become the old false verdict. Both builders return false on an attempted over-budget query, including at budget zero. This yields the proposed budget-induction route. Query widths can be computed from the unary parameter in the raw machine input; a postprocessor that lacks access to that parameter would need an appropriate wrapper. The sketch allows the raw-function construction.

## The eight intended reductions

These are assessments of contract expressiveness. Most prong source files are not in this bundle or the pinned branch; their actual future instantiations and security proofs are not certified.

| Resolution-table site | Concrete use now expressible | Assessment / remaining application obligation |
|---|---|---|
| Thm 135.4 · PRF MAC | Use the companion for the input-free forger. Forward signing queries with `perCall = 1`; retain queried messages in state; finalization queries the proposed forgery message and tests tag equality and freshness. Set `outLen = 1`, `finCall = 1`; use T4. | Usable. The outer budget is `q + 1`, including verification. The finalizer can still query when the forger used no signing queries. |
| Thm 137.2 · Lamport | `advIn` builds the public key from challenge `y = z` and seed; the handler answers the permitted signing query or records an abort; `out` extracts the selected forged preimage or returns failure. | Usable. An abort flag can force failure in `out` even if the simulated adversary continues on a dummy answer. Selection of an index/coin distribution remains an application obligation; T1 does not itself implement an exact uniform sampler on an arbitrary finite set. |
| Thm 144.1 · hash-and-sign B | Construct `(pk,i)` as input, record the signing query, and return the actual pair of colliding messages through `out`. | Usable. T1 preserves the complete collision word, including failure conventions. |
| Thm 144.1 · hash-and-sign C | Construct `(pk,i)` as input; answer signing requests by querying on `h_i(m)`; finalize to the transformed message/signature with `finCall = 0`. | Usable. An oracle-free finalizer still computes and returns its output at budget zero. |
| Thm 168.2 · PRF encryption | Service encryption/challenge requests through the outer PRF; place the hidden bit and needed random tapes in the seed; finalization compares the adversary's guess with that bit; use the companion and T4 where required. | Usable. The inner encoding/budget must include the challenge request, and state must enforce the phase restrictions. |
| Thm 170.4 · CCA2 scheme | Service encryption/decryption requests through the substituted outer function, keeping the other key in the seed; finalize to one bit and use T4. | Usable at the declared corrected widths, including the `2n` domain. State must retain the challenge and enforce refusal of its decryption; the generic contract does not supply that invariant. |
| Thm 175.9 (⇒) · nonmalleability | Give the adversary `pk`, forward allowed decryption calls, then decrypt up to `ℓ` output ciphertexts in finalization and run the distinguisher. Include its coins in the seed and its advice through `z`, then hard-wire/re-pair as necessary. | Usable. For one outer query per forwarded request, the budget is `q + ℓ`. Finalization can depend on all its own answers through its local log. |
| `padded_cpa` · public key | From `z = (pk,c)`, give the adversary `pk`, answer the challenge with the padded ciphertext, and finalize by the required bit flip or zeroing. | Usable as the reduction pattern specified in the resolution. Its prong declaration was not supplied, so its exact application is not independently checked. |

The source checks used book pp. 134–138, 144–145, 168–171 and 175. The Lamport reduction's input construction and final preimage extraction were also checked visually on book p. 138/PDF p. 150. The source's arbitrary-message statements require the appropriate bounded/padded encoding when instantiated through these fixed-width contracts. The contracts do not assert an unrestricted variable-length compiler or support rewinding/multiple adversary executions.

## Adversarial instantiations and independent finite checks

The following attempts use constant functions, parsing, concatenation, bounded logs and bit operations, so their handler functions have straightforward polynomial implementations. The checks are Python models of the displayed definitions, not Lean-elaborated handler instances or proofs of T1/T2/T4.

1. **Nontrivial input and exact non-Boolean final output (T1).** Set the inner budget to zero, the adversary output width to two, and state width to one. Let `advIn` return the negation of the first input bit followed by the seed bit; let the adversary return those two bits; let `out` concatenate `z`, state and adversary output. For `z = [true,false]`, seed `[false]`, state `[true]`, the required machine output is exactly `[true,false,true,false,false]`. It is neither the adversary's raw output nor an acceptance probability. The new T1 states the required equality. Thirty-six finite input/seed/state/parameter cases agreed.

2. **One malformed component (T1), compared with a malformed interactive return.** At answer/state widths one, `run = pairEncode [true] []` gives `(true,false)`, and `run = pairEncode [] [true]` gives `(false,true)`. An interactive tagged return with only one payload bit, when two are required, gives `(false,false)`. This confirms F03/N6 and prevents incorrectly assuming the same failure semantics for both handler types.

3. **Zero per-call and finalization budgets (T2).** A handler returning a valid answer/state without an outer query still executes once; a finalizer returning `[true]` still returns true with `finCall = 0`. No outer query occurs. This validates the corrected activation bound and exposes R2-03.

4. **Finalization after an immediate inner timeout (T2).** Let `q = 0`, let the adversary request an inner query, and let `finCall = 1`. The inner result is the all-false timeout with initial state unchanged, but finalization still performs its outer verification query. The total budget is one. Thus the added finalization is not accidentally skipped on inner timeout.

5. **Repeated local over-budget requests (T2).** With `perCall = 1`, let the handler always request another outer query. Each call makes one actual query, then returns the joint default. Let the finalizer with budget zero negate the adversary output. The final nonzero result is preserved even when all global query budget has been consumed: the outer builder accepts the final return at zero remaining budget. This tests both local and global timeout boundaries.

6. **Two outer oracles, adaptive calls and retained state (T2).** Use one zero-bit query domain and one one-bit query domain, both with one-bit answers. Each inner call queries both oracles adaptively and updates state; finalization queries them again and combines its answers with that state. Direct simulation and a separately written log-replay next-move model agree as complete branching trees, including branches inconsistent with a fixed deterministic oracle. This checks the stronger tree-equality form of T2, not merely final outputs for selected functions.

7. **Arbitrary initial state.** With no inner queries and `out` returning the state, T1 must reproduce `H.init n`. This does not refute the theorem: its target is nonuniform, and the entire initial state is polynomial-length advice. It would refute an unjustified inference of uniformity from these statements.

The executed checks passed:

| Check | Cases and coverage |
|---|---|
| Exact index grammar | 2,555 combinations: `k = 0,…,4`, all words of lengths zero through eight. |
| Complete move decoding | 393,204 combinations: all words through length fourteen, four oracle-width families including no oracle and zero-width domains, and output widths zero through two; also all canonical round trips for those families. |
| T1 input/final-output composition | 36 parameter/input/seed/state combinations. |
| Direct T2 tree versus replay model | 720 comparisons: five handler families, three adversaries, parameters zero/one, three auxiliary inputs, both one-bit seeds, and inner budgets zero through three. Every tree respected `q * perCall + finCall`. |
| T4 move translation | 24,573 cases: query widths zero through two and all words through length twelve, including malformed words. |

These bounded checks supplement the general source reasoning; they do not justify extrapolating a tested bound to all inputs or certify a machine construction.

## Regression assessment and verification limits

The supplied diff contains 20 changed files within the 25-file audit surface. Outside the intentional strict-index change and R-04-3 additions/restatements, no semantic definition change was found. In particular, log order, query-budget boundary behavior, componentwise defaults, old one-oracle evaluation, lazy sampling and D8 execution remain as before. The repaired bridge proof statements retain their conclusions.

Strict index decoding does change the behavior of a *fixed* machine emitting malformed index words. The broader all-machine security interpretation can nevertheless be preserved by polynomial output wrappers: from the old permissive decoder to the strict one, replace a parsed index word by the all-true word of the same length; in the reverse direction, replace a non-unary index word by an invalid move such as `[]`. Logs are canonical in both models. These are explicit normalization arguments, not the invalid inference that universal quantification alone makes arbitrary decoder changes harmless. No new formal normalization theorem is claimed.

The audit read the brief first, checked the full repair diff and the added equation/codec proofs, compared changed contracts and descriptions, and inspected pinned imported definitions needed to interpret efficiency. It did **not** independently run Lean, replay `.olean` files, print axiom dependencies, run the repository linter or execute the seal: no `lean` or `lake` executable was available, and the cited execution logs were omitted. Consequently the pack's “60 modules / zero errors,” “375 standard,” and lint/seal outcomes remain maintainer attestations. Source hashes were independently verified; execution claims were not.

Supplemental sources were read at the audited commit, never the moving default branch:

- [NUPPT and its input/time/advice semantics](https://github.com/Shilun-Allan-Li/tcslib/blob/243598b7cb0c3fdd50b22a92a011f1b77f55c8c6/TCSlib/Complexity/Randomized/PPT.lean).
- [Pre/post-processing, advice and coin-splitting closure](https://github.com/Shilun-Allan-Li/tcslib/blob/243598b7cb0c3fdd50b22a92a011f1b77f55c8c6/TCSlib/Complexity/Randomized/Closure.lean).
- [Pair encoding and decoding](https://github.com/Shilun-Allan-Li/tcslib/blob/243598b7cb0c3fdd50b22a92a011f1b77f55c8c6/TCSlib/Complexity/TuringMachine/Encoding.lean).
- [Fixed-length bit decoding](https://github.com/Shilun-Allan-Li/tcslib/blob/243598b7cb0c3fdd50b22a92a011f1b77f55c8c6/TCSlib/Cryptography/Asymptotic/Adversary.lean).
- [Duplication ledger at the pinned head](https://github.com/Shilun-Allan-Li/tcslib/blob/243598b7cb0c3fdd50b22a92a011f1b77f55c8c6/briefs/pass-shelat-ch5-8/duplication-ledger.md).

The recorded `coinLen` equation and old-decoder case-lemma prerequisites remain obligations before their efficiency-fill consumers are written. The stale design note is not used to override the restated contracts. Closure of this gate would not certify the four deferred efficiency proofs, the future prong instantiations, or the scheduled protocol-view bridges.

## Notation glossary

- `n`: security parameter; `z`: reduction input; `ω`: handler seed; `r`: adversary tape.
- `s`, `a`: handler state and adversary output; `m`: actual number of inner queries on an execution.
- `q(n)`, `perCall(n)`, `finCall(n)`: evaluated inner-query, per-call outer-query and finalization budgets.
- `din(i)`, `dout(i)`: query and answer widths at the fixed parameter in the log-length calculation.
- `ℓ`: number/bound of ciphertexts handled during nonmalleability finalization, as in the resolution table.
- `#outer queries`: number of outer queries along one execution path. Other code names and parameters are the audited Lean identifiers.
