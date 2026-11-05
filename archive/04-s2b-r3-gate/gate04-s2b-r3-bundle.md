## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/pack-r3.md =====

# Gate 04 (Pass–shelat ch. 5–8, S2b), round 3: closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
at its head `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`, after the round 2 repairs (two commits on
`243598b7`). In the bundle:
- round 2's findings (`gate04-s2b-r2-findings.md`);
- the round 2 resolutions (`resolutions-r2.md`);
- the repair diff from `243598b7` (`evidence-r3/repair.diff.txt`);
- **all the execution evidence**: `evidence-r3/{replay.log, replay-order.txt, axioms.log, lint.log,
  check8.log, seal.py.txt, seal-evidence.log}`;
- the round 1 review (`review/gate04-review.md`) and the duplication ledger;
- every changed Lean file at the new head.

The deliverable is **`gate04-s2b-r3-findings.md`**.

## Brief for the auditor

1. For R2-01, R2-02, R2-03 and the round 1 items left open (F02, N2, N7), say whether the resolution
   is adequate: **fixed**, **recorded**, or **not resolved** (say why).
2. Audit the changed surface afresh: the re-proved consumer proofs (they must not read other files'
   definitions; the seal output is the evidence), the new equation lemmas (each states its
   definition's equation and nothing more), and the corrected docstrings. Check the disclosed
   boundary (older ch. 2–4 proofs in `PRF.lean` outside the seal table) is stated accurately. Look
   for regressions.

## Attestations (maintainer; `evidence-r3/`)

- **Elaboration** (`replay.log`): the modules downstream of the files changed since `afe5982f`, in
  import order, from a fresh copy of the `afe5982f` olean tree, at `27ae72da`: results in the log.
- **Axioms** (`axioms.log`): every public theorem of the 25 changed files; `sorryAx` exactly in T1,
  T2, `exists_toCompOn_of_toComp` and T4.
- **Lint** (`lint.log`): 0 findings in each changed file. **Check 8** (`check8.log`): 0 failures,
  0 warnings on `Games/`. **Seal** (`seal-evidence.log`): all 13 consumer files pass.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per item: `R2-01: fixed / recorded / not resolved — <reason>` (also R2-02, R2-03, F02,
N2, N7). Severity guide as in rounds 1–2. The gate closes at **0 blockers and 0 majors**.

## ===== gate04-s2b-r2-findings.md =====

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

## ===== resolutions-r2.md =====

# Gate 04 (S2b, #195): round 2 resolutions

- **Round 2:** findings `findings/gate04-s2b-r2-findings.md` on #195 at `243598b7`: **1 major (R2-01),
  2 minors (R2-02, R2-03)**. F01, F03, F04, F06, N1, N5, N6 fixed; F05 fixed for the accounting
  defect; N3 and N4 recorded; F02, N2 and N7 not resolved (F02 pending R2-01; N2 and N7 because the
  evidence was not in the bundle).
- **Repairs:** two commits on #195's branch after `243598b7`:
  - `81e4f4e21738e90eeef285a2a88fb7f664918a3a`: R2-01 (the seal extended to every consumer file;
    `Simulate.lean` and `PRF.lean` re-proved through published lemmas) and R2-03;
  - `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`: equation lemmas clearing check 8's three warnings.
- **Evidence** (`evidence-r3/`, **all in the bundle this time**): the replay, the axiom printout, lint,
  check 8, the seal script and its full output, the round 1 review, and the duplication ledger.

| Item | Severity | Resolution |
|---|---|---|
| R2-01 | major | **Fixed.** `QueryImpl.passthrough_apply` is proved by `rw [passthrough, ofComp_apply, OracleComp.call_bind]` (its own definition, a same-file lemma, a published lemma). The seal now covers **every consumer file of the change set, the new equation proofs included** (13 files, `seal-evidence.log`): all pass for the current version. To get there, pre-existing proofs were re-proved through published lemmas: in `Simulate.lean`, `simulate_bind`, `simulate_comp`, `simulate_withLog`, `simulate_costBoundedBy` and `simulate_call`; in `PRF.lean`, `acceptProb_random_eq_lazy`, `buildTree_boundedBy`, `toOracleAdversary_boundedBy` and `prfAdv_toOracleAdversary_zero`. New equation lemmas beside their definitions: `OracleAdversary.boundedBy_iff`, `lazyDist_apply`. The seal configuration's one non-definition entry (`abs_sub_le_sum_hybrids`) was removed. **Boundary, disclosed:** older ch. 2–4 proofs in `PRF.lean` (Frederick's, not S2b's) still read `distAdv`, `prfAdv`, `randomFunction`, `PRF` and the GGM reduction's helpers, which are not in the seal table. Gate 03d audits `PRF.lean` and the ch. 2–4 clean-up PR pays this back. |
| R2-02 | minor | **Fixed.** The bundle carries `evidence-r3/{replay.log, replay-order.txt, axioms.log, lint.log, check8.log, seal.py.txt, seal-evidence.log}`, the round 1 review (`review/gate04-review.md`, defining N1–N7) and the duplication ledger (rows DL-9 to DL-19 now exist; DL-9 includes `take_drop_ofFn_blocks`, gate 04 N4). |
| R2-03 | minor | **Fixed.** `InteractiveHandler`, `call` and `finish` (and their equation lemmas' docstrings): "a malformed move, or a further query after the budget is spent, gives the all-`false` result; a return at zero remaining budget is accepted". |
| F02 | major (round 1) | **Fixed with R2-01** (the seal is clean on every consumer file). |
| N2, N7 | minor | **Fixed:** check 8 is now 0 failures and **0 warnings** on `Games/` (the three S2a warnings cleared by `OracleSpec.add_dom_inl/_inr`, `add_rng_inl/_inr`, `sampleFin_eq`, `sample_eq`, `queryImpl_def`), and the seal output is attached. |

## ===== evidence-r3/repair.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/PRF.lean b/TCSlib/Cryptography/Asymptotic/PRF.lean
index d305cd99..3fb90bbb 100644
--- a/TCSlib/Cryptography/Asymptotic/PRF.lean
+++ b/TCSlib/Cryptography/Asymptotic/PRF.lean
@@ -164,16 +164,14 @@ theorem acceptProb_random_eq_lazy {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : Pol
     (hA : A.BoundedBy q) :
     acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
       acceptProb (fun W : Fin q → (Fin (ℓ₂.eval n) → Bool) => extendStream W) (lazyDist A) := by
-  show uprob (fun z : ((Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) × ρ =>
-      (A z.2).eval z.1 = true) =
-    uprob (fun z : (Fin q → (Fin (ℓ₂.eval n) → Bool)) × ρ =>
-      (A z.2).evalLazy (extendStream z.1) [] = true)
-  rw [uprob_prod_comm (fun R (r : ρ) => (A r).eval R = true),
-    uprob_prod_comm (fun W (r : ρ) => (A r).evalLazy (extendStream W) [] = true),
+  rw [acceptProb_def, acceptProb_def,
+    uprob_prod_comm (fun R (r : ρ) => oracleDist A ((OracleEnsemble.random ℓ₁ ℓ₂).O n R) r = true),
+    uprob_prod_comm (fun W (r : ρ) => lazyDist A (extendStream W) r = true),
     uprob_prod, uprob_prod]
   congr 1
   funext r
-  exact (QueryTree.uprob_evalLazy (· = true) (hA r)).symm
+  simp only [OracleEnsemble.random_O, oracleDist_apply, lazyDist_apply]
+  exact (QueryTree.uprob_evalLazy (· = true) ((OracleAdversary.boundedBy_iff A q).1 hA r)).symm
 
 /-! ### Next-query machines as oracle adversaries (D7) -/
 
@@ -264,13 +262,16 @@ theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
     ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
       (buildTree next q hist).BoundedBy q
   | 0, hist => by
-    unfold buildTree
-    cases next hist <;> exact trivial
+    cases h : next hist with
+    | ret b => rw [buildTree_zero_of_ret h]; exact QueryTree.boundedBy_ret b 0
+    | query x => rw [buildTree_zero_of_query h]; exact QueryTree.boundedBy_ret false 0
   | q + 1, hist => by
-    unfold buildTree
-    cases next hist with
-    | ret b => exact trivial
-    | query x => exact fun o => buildTree_boundedBy next q (hist ++ [(x, o)])
+    cases h : next hist with
+    | ret b => rw [buildTree_succ_of_ret h]; exact QueryTree.boundedBy_ret b (q + 1)
+    | query x =>
+      rw [buildTree_succ_of_query h]
+      exact (QueryTree.boundedBy_query_succ x _ q).2
+        fun o => buildTree_boundedBy next q (hist ++ [(x, o)])
 
 /-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
 ([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
@@ -295,7 +296,9 @@ every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggm
 Induction on the budget (`buildTree_boundedBy`). -/
 theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
     (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
-  fun _ => buildTree_boundedBy _ q []
+  (OracleAdversary.boundedBy_iff _ q).2 fun r => by
+    rw [NUPPT.toOracleAdversary_eq]
+    exact buildTree_boundedBy _ q []
 
 /-! ### Oracle indistinguishability [PS10, Definition 96.1] -/
 
@@ -717,15 +720,13 @@ private theorem prfAdv_toOracleAdversary_zero
     | query x => exact ⟨false, rfl⟩
   choose b hb using hA
   have key : ∀ {σ : Type} [Fintype σ] [Nonempty σ] (X : σ → (Fin n → Bool) → (Fin n → Bool)),
-      acceptProb X (oracleDist (D.toOracleAdversary n n n 0)) =
+      uprob (fun z : σ × D.Coins n => (D.toOracleAdversary n n n 0 z.2).eval (X z.1) = true) =
         uprob fun r : D.Coins n => b r = true := by
     intro σ _ _ X
-    unfold acceptProb
     rw [← uprob_snd (α := σ) (fun r : D.Coins n => b r = true)]
     refine uprob_congr fun z => ?_
-    rw [oracleDist, hb z.2]
-    rfl
-  rw [prfAdv, distAdv, key, key, sub_self, abs_zero]
+    rw [hb z.2, QueryTree.eval_ret]
+  rw [prfAdv_eq, key (F n), key (fun R => R), sub_self, abs_zero]
 
 /-- **[PS10, Theorem 97.3] (Goldreich–Goldwasser–Micali): the GGM family of a length-doubling
 pseudorandom generator is a pseudorandom function.**
diff --git a/TCSlib/Cryptography/Games/Efficiency.lean b/TCSlib/Cryptography/Games/Efficiency.lean
index aeb8cff4..cdfa1e0c 100644
--- a/TCSlib/Cryptography/Games/Efficiency.lean
+++ b/TCSlib/Cryptography/Games/Efficiency.lean
@@ -319,8 +319,8 @@ the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queri
 reduction's output in a last phase (`finRun`), both with outer queries.
 
 One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
-`perCall(n) + 1` rounds of `run` (the last returns the answer or, with the budget spent, is cut off
-with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
+`perCall(n) + 1` rounds of `run` (the last returns the answer; a further query after the budget
+is spent is cut off with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
 the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
 `bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
 `⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
@@ -330,7 +330,8 @@ joint default, unlike `PolyHandler.answer`, which defaults each component separa
 The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
 adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
 queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
-output on a malformed round output or a spent budget. -/
+output on a malformed round output or on a further query after the budget is spent. (A return at
+zero remaining budget is accepted: only a query then hits the timeout.) -/
 structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
     (din' dout' : Fin k' → PolyExpr) where
   /-- The length of the state. -/
@@ -391,7 +392,8 @@ theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ)
 
 /-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
 `perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
-is the all-`false` answer and state (`decodeBitMove`'s default), and so is an exhausted budget. -/
+is the all-`false` answer and state (`decodeBitMove`'s default), and so is a further query after
+the budget is spent (a return at zero remaining budget is accepted). -/
 def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
     (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
     (x : Fin ((din i).eval n) → Bool) :
@@ -402,7 +404,7 @@ def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List B
     (zeroBits _) (H.perCall.eval n) []
 
 /-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
-`perCall(n)` and the all-`false` result when it runs out: `H.call n z ω s i x =
+`perCall(n)` and the all-`false` result on a query after it is spent: `H.call n z ω s i x =
 buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
 -/
 theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
@@ -451,7 +453,8 @@ theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
 /-- **The finalization** in the final state `s`, after the adversary's output `a`: the
 reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
 `finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
-(`decodeBitMove`'s default), and so is an exhausted budget. -/
+(`decodeBitMove`'s default), and so is a further query after the budget is spent (a return at
+zero remaining budget is accepted). -/
 def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
     (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
     (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
@@ -462,7 +465,7 @@ def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List
     (zeroBits _) (H.finCall.eval n) []
 
 /-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
-`finCall(n)` and the all-`false` output when it runs out: `H.finish n z ω s a =
+`finCall(n)` and the all-`false` output on a query after it is spent: `H.finish n z ω s a =
 buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
 (H.finCall.eval n) []`. -/
 theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
diff --git a/TCSlib/Cryptography/Games/OracleComp.lean b/TCSlib/Cryptography/Games/OracleComp.lean
index 2b8c0460..f38b9fc3 100644
--- a/TCSlib/Cryptography/Games/OracleComp.lean
+++ b/TCSlib/Cryptography/Games/OracleComp.lean
@@ -166,6 +166,22 @@ def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : Oracle
     OracleSpec (ι₁ ⊕ ι₂) :=
   ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩
 
+/-- The left oracles of the union have the queries of `s₁`: `(s₁.add s₂).dom (.inl i) = s₁.dom i`. -/
+theorem OracleSpec.add_dom_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
+    (s₁.add s₂).dom (.inl i) = s₁.dom i := rfl
+
+/-- The right oracles of the union have the queries of `s₂`: `(s₁.add s₂).dom (.inr j) = s₂.dom j`. -/
+theorem OracleSpec.add_dom_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
+    (s₁.add s₂).dom (.inr j) = s₂.dom j := rfl
+
+/-- The left oracles of the union have the answers of `s₁`: `(s₁.add s₂).rng (.inl i) = s₁.rng i`. -/
+theorem OracleSpec.add_rng_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
+    (s₁.add s₂).rng (.inl i) = s₁.rng i := rfl
+
+/-- The right oracles of the union have the answers of `s₂`: `(s₁.add s₂).rng (.inr j) = s₂.rng j`. -/
+theorem OracleSpec.add_rng_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
+    (s₁.add s₂).rng (.inr j) = s₂.rng j := rfl
+
 namespace OracleComp
 
 variable {ι ι₁ ι₂ : Type} {α β : Type}
diff --git a/TCSlib/Cryptography/Games/Probability.lean b/TCSlib/Cryptography/Games/Probability.lean
index 2b1a5766..9b725fca 100644
--- a/TCSlib/Cryptography/Games/Probability.lean
+++ b/TCSlib/Cryptography/Games/Probability.lean
@@ -79,6 +79,10 @@ variable {α β : Type}
 /-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
 def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure
 
+/-- Sampling `Fin (m + 1)` is one query to the `m`-th sampling oracle:
+`sampleFin m = .query m () .pure`. -/
+theorem sampleFin_eq (m : ℕ) : sampleFin m = .query m () .pure := rfl
+
 /-- A uniformly random element of the nonempty finite type `T`, through its enumeration
 `Fintype.equivFin`. -/
 noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
@@ -86,6 +90,13 @@ noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
     (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
       sampleFin (Fintype.card T - 1)
 
+/-- Sampling `T` is sampling an index below `|T|` and reading it through `Fintype.equivFin`:
+`sample T = (fun j => (equivFin T).symm (Fin.cast _ j)) <$> sampleFin (|T| − 1)`. -/
+theorem sample_eq (T : Type) [Fintype T] [Nonempty T] :
+    sample T = (fun j : Fin (Fintype.card T - 1 + 1) =>
+      (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
+        sampleFin (Fintype.card T - 1) := rfl
+
 /-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
 the `m + 1` equally likely answers at a sampling step. -/
 noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
diff --git a/TCSlib/Cryptography/Games/Simulate.lean b/TCSlib/Cryptography/Games/Simulate.lean
index 906ec1ac..e8c957dc 100644
--- a/TCSlib/Cryptography/Games/Simulate.lean
+++ b/TCSlib/Cryptography/Games/Simulate.lean
@@ -69,6 +69,11 @@ on oracle `i`, query `x` and state `s`, a computation returning the answer and t
 def QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
   ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)
 
+/-- An implementation is a function of the oracle, the query and the state:
+`QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. -/
+theorem queryImpl_def {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :
+    QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ) := rfl
+
 /-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
 threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
 def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
@@ -98,13 +103,14 @@ monad's associativity lines up the continuations. -/
 theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
     simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
   induction c generalizing s with
-  | pure a => rfl
+  | pure a => simp only [OracleComp.pure_bind, simulate_pure]
   | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]
 
 /-- Simulating a single call is running the implementation. -/
 theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
     simulate impl (OracleComp.call i x) s = impl i x s := by
-  simp only [OracleComp.call, simulate_query, simulate_pure]
+  rw [← OracleComp.bind_pure (OracleComp.call i x), OracleComp.call_bind, simulate_query]
+  simp only [simulate_pure]
   exact OracleComp.bind_pure _
 
 end Simulate
@@ -130,8 +136,8 @@ def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
 /-- Forwarding asks the same oracle the same query and keeps the state:
 `passthrough i x s = .query i x (fun y => .pure (y, s))`. -/
 theorem passthrough_apply {spec : OracleSpec ι} (i : ι) (x : spec.dom i) (s : σ) :
-    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) :=
-  rfl
+    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) := by
+  rw [passthrough, ofComp_apply, OracleComp.call_bind]
 
 /-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
 `impl₁`, and `.inr j` by `impl₂`. -/
@@ -192,7 +198,7 @@ theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec 
     simulate impl₂ (simulate impl₁ c s₁) s₂ =
       (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
   induction c generalizing s₁ s₂ with
-  | pure a => rfl
+  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
   | query i x k ih =>
     simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
       OracleComp.pure_bind]
@@ -233,7 +239,7 @@ theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
       simulate impl c s := by
   induction c generalizing s log with
-  | pure a => rfl
+  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
   | query i x k ih =>
     simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
     congr 1
@@ -257,10 +263,14 @@ theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
     OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
   induction c generalizing q s with
-  | pure a => trivial
+  | pure a =>
+    rw [simulate_pure]
+    exact OracleComp.costBoundedBy_pure cost' (a, s) q
   | query i x k ih =>
-    obtain ⟨hi, hk⟩ := hc
+    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query b i x k q).1 hc
     have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
-    rwa [Nat.add_sub_cancel' hi] at h
+    rw [Nat.add_sub_cancel' hi] at h
+    rw [simulate_query]
+    exact h
 
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean b/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
index 9c785839..caad88a0 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
@@ -211,6 +211,12 @@ def OracleAdversary.BoundedBy {ρ : Type*} {I O : Type}
     (A : OracleAdversary ρ I O) (q : ℕ) : Prop :=
   ∀ r, (A r).BoundedBy q
 
+/-- `A` makes at most `q` queries iff the tree of every coin string does:
+`A.BoundedBy q ↔ ∀ r, (A r).BoundedBy q`. -/
+theorem OracleAdversary.boundedBy_iff {ρ : Type*} {I O : Type} (A : OracleAdversary ρ I O)
+    (q : ℕ) : A.BoundedBy q ↔ ∀ r, (A r).BoundedBy q :=
+  Iff.rfl
+
 /-- The oracle adversary `A` as a distinguisher for oracles: on the oracle `f` and coins
 `r` it outputs the result of running `A r` against `f`. With a sampler for the oracle,
 `acceptProb` of this distinguisher is the probability `Pr[A^f = 1]` of
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean b/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
index f09a5e55..9ad01f03 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
@@ -81,6 +81,13 @@ noncomputable def subHybridStream {q : ℕ} (G : S → V) (j : ℕ)
 def lazyDist (A : OracleAdversary ρ P V) : (ℕ → V) → ρ → Bool :=
   fun a r => (A r).evalLazy a []
 
+omit [Fintype P] [Fintype V] [Nonempty V] [Fintype ρ] in
+/-- On the answer stream `a` and coins `r`, `lazyDist A` is the lazy run of `A r` from the empty
+list of distinct queries: `lazyDist A a r = (A r).evalLazy a []`. -/
+theorem lazyDist_apply (A : OracleAdversary ρ P V) (a : ℕ → V) (r : ρ) :
+    lazyDist A a r = (A r).evalLazy a [] :=
+  rfl
+
 /-- The probability that `A` accepts in the sub-hybrid `H_j`: `j` uniform values and
 `q - j` generator outputs answer the distinct queries in order. [Gar26, proof of
 Theorem 3.3, `H_{i,j}`] with the level `i` abstracted away; see the module docstring for

## ===== evidence-r3/replay.log =====

# maintainer replay at 27ae72da62119ebdde380b8cb2d8c183b59fa2bf: the 60 modules downstream of the 21 Lean files changed since afe5982f, in import order, from a fresh copy of the afe5982f olean tree
TCSlib/Cryptography/Games/OracleComp rc=0 1s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/Defs rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/GGM rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 39s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Simulate rc=0 0s errors=0 sorry=0
TCSlib/Cryptography/Games/Advantage rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Hopping rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Protocols rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Machines rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/BitCodec rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/QueryTree rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/Machines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Efficiency rc=0 3s errors=0 sorry=4
TCSlib/Cryptography/Games/Bridges/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/Strategies rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges rc=0 3s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 93s errors=0 sorry=0
# done 2026-11-05T21:37:10Z

## ===== evidence-r3/replay-order.txt =====

TCSlib/Cryptography/Games/OracleComp
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling
TCSlib/Cryptography/Pseudorandom/Functions/Defs
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids
TCSlib/Cryptography/Pseudorandom/Functions/GGM
TCSlib/Cryptography/Pseudorandom/Functions
TCSlib/Cryptography/Pseudorandom
TCSlib/Cryptography/Asymptotic/PRFLemmas
TCSlib/Cryptography/Asymptotic/GGMReduction
TCSlib/Cryptography/Asymptotic/GGMReductionEval
TCSlib/Cryptography/Asymptotic/PRF
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas
TCSlib/Cryptography/Asymptotic/MultiMessage
TCSlib/Cryptography/Asymptotic
TCSlib/Cryptography/ZeroKnowledge/Interaction
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs
TCSlib/Cryptography/ZeroKnowledge/Defs
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas
TCSlib/Cryptography/ZeroKnowledge/Commitment
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring
TCSlib/Cryptography/ZeroKnowledge/NPLemmas
TCSlib/Cryptography/ZeroKnowledge/NP
TCSlib/Cryptography/ZeroKnowledge
TCSlib/Cryptography/Games/Probability
TCSlib/Cryptography/Games/Simulate
TCSlib/Cryptography/Games/Advantage
TCSlib/Cryptography/Games/Hopping
TCSlib/Cryptography/Games/Protocols
TCSlib/Cryptography/Games
TCSlib/Cryptography/Games/Machines
TCSlib/Cryptography/Games/BitCodec
TCSlib/Cryptography/Games/Bridges/QueryTree
TCSlib/Cryptography/Games/Bridges/Machines
TCSlib/Cryptography/Games/Efficiency
TCSlib/Cryptography/Games/Bridges/Experiments
TCSlib/Cryptography/Games/Bridges/Strategies
TCSlib/Cryptography/Games/Bridges
audits/pass-shelat/Checks

## ===== evidence-r3/axioms.log =====

# #print axioms for every public theorem of the 26 Lean files #195 changes against a3c5fa8b (TCSlib.lean facade excluded), at 27ae72da62119ebdde380b8cb2d8c183b59fa2bf: 410 theorems, 406 standard; sorryAx exactly in T1, T2, exists_toCompOn_of_toComp, T4
'TCSlib.Cryptography.eval_chainTree' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.boundedBy_chainTree' depends on axioms: [propext]
'TCSlib.Cryptography.multiMsgAdv_boundedBy' depends on axioms: [propext]
'TCSlib.Cryptography.acceptProb_oracleDist_multiMsgAdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfAdv_multiMsgAdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_not_injective_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.pushesUniform_comp_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_otpEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_prfEncReal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_prfEncFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_prfDecWF' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_prfDecFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.runAt_prfEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.runAt_prfDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decodeFin_runAt_prfDec_of_not_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encodeTuple_eq_flatten' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.prfScheme_multiEncDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfScheme_multiMessageSecure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_multiMessageSecure_of_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.abs_uexp_le_uexp_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.abs_uexp_sub_le_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.card_filter_lt_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.uprob_eq_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.negligible_choose_div_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.acceptProb_oracleDist_congr_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.MultiMsg.prfAdv_congr_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.length_histBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.encodeHist_eq_flatMap' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.eval_histBlockLen' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.length_flatMap_of_length' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.flatMap_range_blocks' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.flatMap_const_singleton' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.flatMap_const_replicate' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.pairFstD_pairFstD_histBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.length_maskBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.dbl_append' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.zipWith_xor_replicate_false' does not depend on any axioms
'TCSlib.Cryptography.MultiMsg.zipWith_xor_dbl' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.zipWith_xor_flatten_ofFn' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.polyTimeComputable_blockMapFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.polyTimeComputable_preFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.polyTimeComputable_postFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.length_flatten_of_length' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.length_maskOf' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.decodeOracleMove_query' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.decodeOracleMove_ret' does not depend on any axioms
'TCSlib.Cryptography.MultiMsg.postFun_layout' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.flatMap_ofFn' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.preFun_encodeHist' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OracleEnsemble.random_O' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OracleEnsemble.keyed_O' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_random_eq_lazy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encodeHist_nil' does not depend on any axioms
'TCSlib.Cryptography.encodeHist_cons' does not depend on any axioms
'TCSlib.Cryptography.buildTree_zero_of_ret' does not depend on any axioms
'TCSlib.Cryptography.buildTree_zero_of_query' does not depend on any axioms
'TCSlib.Cryptography.buildTree_succ_of_ret' does not depend on any axioms
'TCSlib.Cryptography.buildTree_succ_of_query' does not depend on any axioms
'TCSlib.Cryptography.buildTree_boundedBy' does not depend on any axioms
'Complexity.NUPPT.toOracleAdversary_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.toOracleAdversary_boundedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OracleEnsemble.Indist.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OracleEnsemble.Indist.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OracleEnsemble.Indist.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.oracle_hybrid_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfAdv_toOracleAdversary' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRF.negligible_prfAdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.DoublingPRG.negligible_prgAdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.two_mul_add_one_expands' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PRG.doubling_apply' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PRG.Secure.truncate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRG.Secure.doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmPRF_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_ggmPRF_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_97_3_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_97_3_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_ggmBitsDist_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmPRF_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_prf_of_exists_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.take_ofFn_castLE' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.drop_take_ofFn_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ofFn_prefixAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.take_ofFn_splitHalves' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.drop_ofFn_splitHalves' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.selHalf_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_selHalf_le' depends on axioms: [propext]
'TCSlib.Cryptography.selHalf_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.preFun_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.coins_preComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.runAtL_preComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.runAt_preComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_castLE' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRG.Secure.truncateTo_easy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRG.Secure.truncateTo_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmFrom_eq_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_ggmStep_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.length_ggmStep_iterate_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.ggmStep_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmStep_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmEval_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmEval_ofFn_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmEval_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.invProb_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.predProb_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_comp_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_comp_eq_sum_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_eq_uexp_sum_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.abs_sum_sub_le_statDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_le_statDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uexp_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_eq_card_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_eq_uexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_exists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_comp_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.half_le_uprob_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.abs_sub_le_sum_hybrids' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_hybrid_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.exists_advantage_hybrid_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.guessGame_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_guessGame' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.guessAdv_eq_half_advantage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.bitSpec_dom' does not depend on any axioms
'TCSlib.Cryptography.Games.bitSpec_rng' does not depend on any axioms
'TCSlib.Cryptography.Games.decodeIdx_replicate' depends on axioms: [propext]
'TCSlib.Cryptography.Games.decodeIdx_eq_some_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Games.decodeIdx_eq_none_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Games.zeroBits_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.ofFn_zeroBits' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.encodeBitMove_query' does not depend on any axioms
'TCSlib.Cryptography.Games.encodeBitMove_ret' does not depend on any axioms
'TCSlib.Cryptography.Games.bitCodec_decodeMove' does not depend on any axioms
'TCSlib.Cryptography.Games.bitCodec_encodeEntry' does not depend on any axioms
'TCSlib.Cryptography.Games.bitCodec_timeout' does not depend on any axioms
'TCSlib.Cryptography.Games.encodeLog_bitCodec' does not depend on any axioms
'TCSlib.Cryptography.Games.decodeBitMove_query' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.decodeBitMove_ret' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.decodeBitMove_eq_query_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.decodeBitMove_of_not_canonical' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.decodeBitMove_encodeBitMove' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.encodeBitMove_injective' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.prob_sample_eq_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.expect_sample_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.prob_sample_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.invProb_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.predProb_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.acceptGame_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.acceptProb_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.distAdv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.singleCodec_decodeMove' does not depend on any axioms
'TCSlib.Cryptography.Games.singleCodec_encodeEntry' does not depend on any axioms
'TCSlib.Cryptography.Games.singleCodec_timeout' does not depend on any axioms
'TCSlib.Cryptography.Games.toHist_nil' does not depend on any axioms
'TCSlib.Cryptography.Games.toHist_cons' does not depend on any axioms
'TCSlib.Cryptography.Games.toHist_append_singleton' depends on axioms: [propext]
'TCSlib.Cryptography.Games.encodeLog_singleCodec' does not depend on any axioms
'TCSlib.Cryptography.Games.buildComp_singleCodec' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.toComp_singleCodec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.evalFn_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.evalFn_query' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_ofComp_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.eval_eq_evalFn' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.treeImpl_apply' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.simulate_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.costBoundedBy_iff_boundedBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.Bridge.turnParty_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.waitParty_none' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.waitParty_some_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.waitParty_some_succ' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.turnParty_succ' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.alt_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.alt_succ' does not depend on any axioms
'TCSlib.Cryptography.Games.Bridge.alt_succ_last' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.exec_turnParty' depends on axioms: [propext]
'TCSlib.Cryptography.Games.Bridge.exec_eq_alt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Bridge.exec_strategies' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.bitSpecAt_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Games.seedIn_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.PolyHandler.input_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.PolyHandler.advInput_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.PolyHandler.result_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.PolyHandler.answer_of_pairDecode_eq_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.PolyHandler.answer_of_pairDecode_eq_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.PolyHandler.answer_of_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.PolyHandler.impl_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.exists_handlerMachine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.InteractiveHandler.input_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.InteractiveHandler.advInput_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.InteractiveHandler.call_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.InteractiveHandler.impl_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.InteractiveHandler.finInput_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.InteractiveHandler.finish_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.exists_interactiveHandlerMachine' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.exists_toCompOn_of_toComp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.exists_toOracleAdversary_of_bitCodec' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_one_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_zero_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.abs_prob_sub_le_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.simulate_allOutputs_bad' depends on axioms: [propext]
'TCSlib.Cryptography.Games.prob_eq_until_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.identical_until_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.hagree_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.identical_until_bad_init' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.MachineCodec.encodeLog_nil' does not depend on any axioms
'TCSlib.Cryptography.Games.MachineCodec.encodeLog_cons' does not depend on any axioms
'TCSlib.Cryptography.Games.buildComp_zero_of_ret' does not depend on any axioms
'TCSlib.Cryptography.Games.buildComp_zero_of_query' does not depend on any axioms
'TCSlib.Cryptography.Games.buildComp_succ_of_ret' does not depend on any axioms
'TCSlib.Cryptography.Games.buildComp_succ_of_query' does not depend on any axioms
'TCSlib.Cryptography.Games.buildComp_costBoundedBy' does not depend on any axioms
'Complexity.NUPPT.toComp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.toComp_costBoundedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.toCompOn_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.toCompOn_costBoundedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.bind_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_eq_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.map_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.query_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.bind_pure' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.bind_assoc' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.call_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.singleSpec_dom' does not depend on any axioms
'TCSlib.Cryptography.Games.singleSpec_rng' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_dom_inl' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_dom_inr' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_rng_inl' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_rng_inr' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.liftLeft_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.liftRight_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_query' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.bind' depends on axioms: [propext]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftLeft' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftRight' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.allOutputs_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.allOutputs_query' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.allOutputs_true' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.bind' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.sampleFin_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.sample_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_query' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sampleFin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.dist_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ExecOutcome.swap_done' does not depend on any axioms
'TCSlib.Cryptography.Games.ExecOutcome.swap_outOfFuel' does not depend on any axioms
'TCSlib.Cryptography.Games.ExecOutcome.swap_sentAfterEnd' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.step_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.step_send' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.step_coin' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.close_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.close_send' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.close_coin' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.endWith_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.endWithT_ne_outOfFuel' depends on axioms: [propext]
'TCSlib.Cryptography.Games.Party.execT_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Party.stepT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.closeT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.endWithT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.execT_outcome' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.queryImpl_def' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_query' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_call' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.QueryImpl.ofComp_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.passthrough_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.sum_inl' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.sum_inr' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.comp_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_comp' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.QueryImpl.withLog_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_withLog' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_costBoundedBy' depends on axioms: [propext]
'TCSlib.Cryptography.prfAdv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfAdv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmFrom_of_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.ggmFrom_of_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.hybridProb_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.hybridProb_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.hybridProb_eq_level_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.hybridProb_eq_level_random' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.hybridProb_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggm_prfAdv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_ggm_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_ggmBitsDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmBits_prfAdv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_ggmBits_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_prod_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_sections_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_update_absorb' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_update_absorb'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_update_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.noteQuery_of_mem' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.noteQuery_of_not_mem' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.idxOf_noteQuery_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.length_noteQuery_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.evalLazy_ret' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.evalLazy_query' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.evalLazy_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.evalLazy_comp' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.extendStream_update_of_ne' depends on axioms: [Classical.choice]
'TCSlib.Cryptography.QueryTree.extendStream_update_self' depends on axioms: [propext, Classical.choice]
'TCSlib.Cryptography.QueryTree.uprob_evalLazy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.induct_ret' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.induct_query' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.eval_ret' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.eval_query' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.boundedBy_ret' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.boundedBy_query_zero' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.boundedBy_query_succ' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.BoundedBy.mono' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.QueryTree.simulate_ret' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.simulate_query' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.eval_simulate' does not depend on any axioms
'TCSlib.Cryptography.QueryTree.BoundedBy.simulate' does not depend on any axioms
'TCSlib.Cryptography.OracleAdversary.boundedBy_iff' does not depend on any axioms
'TCSlib.Cryptography.oracleDist_apply' does not depend on any axioms
'TCSlib.Cryptography.lazyDist_apply' depends on axioms: [propext]
'TCSlib.Cryptography.acceptProb_tableDist_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_tableDist_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.subHybridProb_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.subHybridProb_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.table_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.encodeMsgs_nil' does not depend on any axioms
'TCSlib.Cryptography.Strategy.encodeMsgs_cons' does not depend on any axioms
'TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.Efficient.exists_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.ReadsPrefix.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.moverIsV_true' does not depend on any axioms
'TCSlib.Cryptography.moverIsV_false' does not depend on any axioms
'TCSlib.Cryptography.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.exec_length' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Strategy.out_eq' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_V' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_P' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_rounds' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_verifierFirst' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_self' does not depend on any axioms
'TCSlib.Cryptography.Protocol.transcriptWith_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.transcript_eq_transcriptWith' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outP_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.viewV_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.viewP_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outP_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.transcript_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_withV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.exists_proverCoins_le' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== evidence-r3/lint.log =====

# scripts/style_lint.py on the 26 Lean files #195 changes against a3c5fa8b, at 27ae72da62119ebdde380b8cb2d8c183b59fa2bf
TCSlib/Cryptography/Asymptotic/MultiMessage.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/PRF.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean: 0 findings in 1 files
TCSlib/Cryptography/Foundations/Experiments.lean: 0 findings in 1 files
TCSlib/Cryptography/Foundations/Probability.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Advantage.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/BitCodec.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/Experiments.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/Machines.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/QueryTree.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/Strategies.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Efficiency.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Hopping.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Machines.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/OracleComp.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Probability.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Protocols.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Simulate.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean: 0 findings in 1 files
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean: 0 findings in 1 files

## ===== evidence-r3/check8.log =====

# scripts/campaign_style_lint.py --check8b on TCSlib/Cryptography/Games at 27ae72da62119ebdde380b8cb2d8c183b59fa2bf
style_lint: 0 FAIL, 0 WARN over 14 files

## ===== evidence-r3/seal.py.txt =====

"""Rule-10 seal self-check: compile each consumer file (current and HEAD versions) with
`attribute [local irreducible]` on the other files' definitions it consumes."""
import subprocess, sys, os
from pathlib import Path
WT = Path("/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/wt-s2b-fix")
OUT = Path("/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout")
OL = "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/s2bfix-r-oleans"
G = "TCSlib.Cryptography.Games."
C = "TCSlib.Cryptography."
SEALS = {
 "TCSlib/Cryptography/Games/Machines.lean": [G+"OracleComp.CostBoundedBy", G+"OracleComp.bind"],
 "TCSlib/Cryptography/Games/Hopping.lean": [G+"OracleComp.AllOutputs", G+"simulate",
    G+"ProbComp.expect", G+"ProbComp.prob", G+"OracleComp.bind"],
 "TCSlib/Cryptography/Games/Protocols.lean": [G+"OracleComp.AllOutputs"],
 "TCSlib/Cryptography/Games/BitCodec.lean": [C+"decodeFin", "Turing.pairDecode",
    "Turing.pairEncode", G+"MachineCodec.encodeLog"],
 "TCSlib/Cryptography/Games/Efficiency.lean": [C+"decodeFin", "Turing.pairDecode",
    "Turing.pairEncode", G+"buildComp", G+"decodeBitMove", G+"bitCodec",
    G+"MachineCodec.encodeLog", G+"zeroBits"],
 "TCSlib/Cryptography/Games/Bridges/Machines.lean": [G+"MachineCodec.encodeLog", G+"buildComp",
    "Complexity.NUPPT.toComp", "Complexity.NUPPT.toCompOn", C+"encodeHist", C+"buildTree",
    "Complexity.NUPPT.toOracleAdversary", C+"decodeOracleMove", G+"OracleComp.bind"],
 "TCSlib/Cryptography/Games/Bridges/QueryTree.lean": [G+"simulate", G+"QueryImpl.ofComp",
    G+"OracleComp.bind", G+"OracleComp.call", C+"QueryTree.eval", C+"QueryTree.simulate",
    G+"OracleComp.CostBoundedBy", C+"QueryTree.BoundedBy", C+"QueryTree.induct"],
 "TCSlib/Cryptography/Games/Bridges/Experiments.lean": [G+"accept", G+"advantage", C+"invProb",
    C+"predProb", C+"acceptProb", C+"distAdv", C+"uprob", G+"ProbComp.sample",
    G+"ProbComp.expect", G+"ProbComp.prob", G+"OracleComp.bind"],
 "TCSlib/Cryptography/Games/Simulate.lean": [G+"OracleComp.bind", G+"OracleComp.call",
    G+"OracleComp.CostBoundedBy"],
 "TCSlib/Cryptography/Games/Advantage.lean": [G+"ProbComp.prob", G+"ProbComp.expect",
    G+"ProbComp.sample", G+"OracleComp.bind"],
 "TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean": [G+"OracleComp.bind"],
 "TCSlib/Cryptography/Asymptotic/PRF.lean": [C+"QueryTree.BoundedBy", C+"QueryTree.eval",
    C+"oracleDist", C+"OracleAdversary.BoundedBy", G+"OracleComp.bind"],
 "TCSlib/Cryptography/Games/Bridges/Strategies.lean": [G+"Party.exec", G+"Party.step",
    G+"Party.close", G+"Party.endWith", G+"ExecOutcome.swap", G+"OracleComp.bind", C+"exec",
    C+"moverIsV", C+"Protocol.outP", C+"Protocol.outV", C+"Protocol.transcriptWith",
    C+"Protocol.transcript"],
}
env = dict(os.environ)
lp = [OL] + [str(d) for d in (WT / ".lake/packages").glob("*/.lake/build/lib/lean")]
env["LEAN_PATH"] = ":".join(lp)
env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env["PATH"]

def seal(src, names):
    lines = src.splitlines()
    idx = max(i for i, l in enumerate(lines[:20]) if l.startswith("set_option"))
    lines.insert(idx + 1, "attribute [local irreducible] " + " ".join(names))
    return "\n".join(lines) + "\n"

def run(text, tag):
    f = OUT / (tag + ".lean")
    f.write_text(text)
    r = subprocess.run(["lean", str(f)], cwd=WT, env=env, capture_output=True, text=True)
    errs = [l for l in (r.stdout + r.stderr).splitlines() if "error" in l]
    return r.returncode == 0 and not errs, errs

which = sys.argv[1:] or list(SEALS)
for path in which:
    names = SEALS[path]
    tag = path.replace("/", "_")[:-5]
    cur = (WT / path).read_text()
    ok, errs = run(seal(cur, names), tag + "_sealed_new")
    head = subprocess.run(["git", "show", "HEAD:" + path], cwd=WT, capture_output=True,
                          text=True).stdout
    ok0, errs0 = run(seal(head, names), tag + "_sealed_old")
    print(f"{path}: sealed current {'PASS' if ok else 'FAIL'}; "
          f"sealed HEAD version {'PASS' if ok0 else 'FAIL'} ({len(errs0)} error lines)")
    for e in errs[:8]:
        print("   cur:", e[:220])
    for e in errs0[:4]:
        print("   old:", e[:220])

## ===== evidence-r3/seal-evidence.log =====

# rule-10 seal check at 81e4f4e21738e90eeef285a2a88fb7f664918a3a (seal.py: each consumer file compiled with `attribute [local irreducible]` on the other files' definitions it consumes; current version and the version at the previous head 243598b7)
TCSlib/Cryptography/Games/Machines.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Hopping.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Protocols.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/BitCodec.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Efficiency.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Bridges/Machines.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Bridges/QueryTree.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Bridges/Experiments.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Games/Simulate.lean: sealed current PASS; sealed HEAD version FAIL (6 error lines)
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Games_Simulate_sealed_old.lean:102:14: error: Tactic `rfl` failed: The left-hand side
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Games_Simulate_sealed_old.lean:135:2: error: Type mismatch
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Games_Simulate_sealed_old.lean:196:14: error: Tactic `rfl` failed: The left-hand side
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Games_Simulate_sealed_old.lean:237:14: error: Tactic `rfl` failed: The left-hand side
TCSlib/Cryptography/Games/Advantage.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)
TCSlib/Cryptography/Asymptotic/PRF.lean: sealed current PASS; sealed HEAD version FAIL (7 error lines)
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Asymptotic_PRF_sealed_old.lean:168:2: error: 'show' tactic failed, pattern
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Asymptotic_PRF_sealed_old.lean:269:24: error: Type mismatch
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Asymptotic_PRF_sealed_old.lean:269:24: error: Type mismatch
   old: /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r3/sealout/TCSlib_Cryptography_Asymptotic_PRF_sealed_old.lean:273:15: error: Type mismatch
TCSlib/Cryptography/Games/Bridges/Strategies.lean: sealed current PASS; sealed HEAD version PASS (0 error lines)

## ===== evidence-r3/changed-files.txt =====

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
TCSlib/Cryptography/Games/Probability.lean
TCSlib/Cryptography/Games/Protocols.lean
TCSlib/Cryptography/Games/Simulate.lean
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean

## ===== review/gate04-review.md =====

# Gate 04 (S2b): review of the auditor's findings, with resolution proposals

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/04-s2b/findings/gate04-s2b-findings.md`: 0 blockers, 2 majors (F01, F02), 4 minors (F03–F06).
- **Code:** worktree `wt-s2b` at `afe5982f612081bba2fbcec9ab41adcbbc118b13` (confirmed with `git rev-parse HEAD`). Line numbers refer to that commit unless a prong worktree is named. The F-1 baseline is `a3c5fa8b`.
- **Downstream code read:**
  - `wt-prong-a` at `2d7b5441` (`Authentication/`);
  - `wt-prong-b` at `c04d8a3a` (`SecureComputation/`, including `Yao.lean`);
  - `wt-prong-c` at `aa71d0e7` (`Composability/`);
  - `wt-prong-d` at `6ea900ae` (`Randomness/`).

  Prongs A–C branch from earlier S2b commits. Their `Games/{BitCodec, Machines, Bridges/*, Protocols, OracleComp}.lean` are byte-identical to `afe5982f`; only `Efficiency.lean` differs (no T2).
- **Method.** I did not build Lean. I did three things:
  - read every S2b proof that consumes another file's definition;
  - ran a script that lists every `unfold`/`simp`/`rw` argument naming a TCSlib definition from another file (scratch tools in `scratchpad/g04-review-tools/`);
  - ran the campaign lint's check 8 (`scripts/campaign_style_lint.py --check8b`) on `TCSlib/Cryptography` at the base `a3c5fa8b` and at the head, and diffed the two.

  Reads through `rfl`, `show` and term-mode definitional unfolding were found by hand. They are what the campaign's rule-10 seal (`attribute [local irreducible]`, `WORKFLOW.md` §"Standing rules") would reject.

## Summary

- **All six findings are true.** I agree with every severity: F01 and F02 are major; F03–F06 are minor.
- **F01 (`decodeIdx` checks only the length).**
  - Confirmed at `BitCodec.lean:60–61`.
  - The fix is a strict unary check with converse lemmas, about 60–90 lines in `BitCodec.lean`.
  - It re-proves one lemma (`decodeIdx_replicate`). No other proof in S2b or in any prong unfolds or reasons about `decodeIdx` or `decodeBitMove`.
  - No statement text changes. Every security notion that uses `bitCodec` quantifies over all NUPPT adversaries, and a coin-preserving post-processing (`exists_comp`) maps each adversary to one with the same computation under the other decoder. So no notion changes meaning.
  - The fix matters most for the efficiency fill. Without converse lemmas the fill cannot read `decodeBitMove` on arbitrary machine output without unfolding it (rule 10).
  - Ruling R-04-1 (light): it changes a T0 definition before the fill is issued.
- **F02 (missing defining equations): true, and understated.** The auditor names 5 consumer sites, in 4 proofs. I find 16 S2b proofs that read another file's TCSlib definitions:
  - the unfolds the auditor names;
  - B2 rewriting with `accept` and `advantage` (`Bridges/Experiments.lean:119,127`);
  - B1 unfolding `QueryImpl.ofComp` and reading `QueryTree.simulate` through `rfl`/`show` (`Bridges/QueryTree.lean:76–77,103–108`);
  - B4 reading `Party.exec`, `step`, `close`, `endWith` and `ExecOutcome.swap` through `rfl`/`show` (`Bridges/Strategies.lean:138–145`), and `simp [moverIsV]` although `moverIsV_true`/`_false` exist (`:163`);
  - `AllOutputs`, which S2b moved from `Hopping.lean` to `OracleComp.lean`. That move turned same-file reads in `Hopping.lean:85,88,168` and `Protocols.lean:238,262–268` into cross-file reads.

  The fix is about 75–85 equation lemmas (mostly `rfl`/`Iff.rfl`, about 450–510 lines with docstrings), with 16 proofs re-pointed. The full list is in §2.

  Prong B would also benefit:
  - at 9 sites that read ch. 2–4's `Protocol.transcriptWith`/`outP`/`outV`/`viewP`/`viewV` (`Interaction.lean`);
  - from 5 lemmas on its own `keyAt`, `garbledValues`, `inputKeys`, `tableAt` and `answersB`, which `Yao.lean` now reads through four private `rfl` copies and one `show`; these should become shared lemmas.

  Ruling R-04-2 decides scope (S2a and ch. 2–4 files would join the change set).
- **What the auditor missed (§5).** The most important miss is N1, proposed **major**:
  - **N1: T1/T2 do not cover the reductions they are cited for.** The auditor listed T1/T2's limitations but did not count them. They lack:
    - adversary input (`toCompOn`);
    - final state and finalization;
    - exact output;
    - a codec bridge to the PRF assumption's `toOracleAdversary`.

    Eight reduction sketches in prongs A and C cite T1 or T2 for reductions that need one of these:
    - Thm 135.4, Thm 137.2 and Thm 144.1 (two machines) in prong A;
    - Thm 168.2, Thm 170.4, Thm 175.9 and `padded_cpa` in prong C.

    Seven of the eight cite T1. Four of those seven need an oracle, which T1's handler cannot query.

    Ruling R-04-3: extend T0–T2 before the fill brief is issued (recommended).
  - **N2:** attestation 4 ran main's per-file `style_lint.py`, which has no check 8. The campaign lint's check 8 shows S2b adding 16 public definitions with no lemma (`workflow.md` §6: "a landing adds no name to it"). It also shows 8 more definitions that pass only by name (a bound or a single case, not an equation).
  - **Minor misses:**
    - N3: the `Strategies.lean` docstring promises results "stated in a later part of this file" that do not exist.
    - N4: `MultiMessageLemmas.take_drop_ofFn_blocks` duplicates `EnsembleLemmas.take_drop_ofFn_blocks` and is not in the duplication ledger.
    - N5: `simp [Option.elim]`, a core definition passed to `simp`, at `Protocols.lean:239`.
    - N6: T1's componentwise default disagrees with T2's joint default (folded into F03).
    - N7: there is no rule-10 seal evidence in the pack.
- **Rulings needed:** R-04-1 (F01), R-04-2 (F02 scope) and R-04-3 (N1). F03–F06 and N2–N7 are maintainer fixes.
- **Proposed closing condition:** F01 and F02 fixed, R-04-3 ruled (and applied if option 1), and the evidence refreshed (§7). Then a delta re-audit of `BitCodec.lean`, `Efficiency.lean` and the new lemmas.

---

## 1. F01 (major): `decodeIdx` checks only the length of the unary index

### Verdict: **true**. Severity: **major (agree)**.

**Evidence at `afe5982f`:**
- `BitCodec.lean:60–61`:
  `def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) := if h : iw.length < k then some ⟨iw.length, h⟩ else none`.
  The bits of `iw` are never read, so `decodeIdx 2 [false] = some ⟨1, _⟩`.
- What the documentation says:
  - module doc `:20–23`: a query is `⟨[false], ⟨1^i, x⟩⟩`, and "anything else, a malformed or wrong-length string, decodes to the all-`false` output";
  - `decodeBitMove`'s docstring `:73–75`: "anything else is the output `zeroBits dα`".
- With `din 1 = 1`, the word `pairEncode [false] (pairEncode [false] [false])` reaches `decodeIdx 2 [false] = some 1` and then `decodeFin 1 [false] = some _` (`:82–85`). So it decodes as `.query 1 _`, not as the default.
- The only lemmas are the forward round trips: `decodeIdx_replicate` (`:64`), `decodeBitMove_query` (`:105`) and `decodeBitMove_ret` (`:112`). Nothing characterizes what is accepted.

I agree with the auditor's scope remark. The alias still has length `i < k`, still costs one query, and the same move can be emitted canonically. So there is no cryptographic attack. The defect is that the decoder does not follow the grammar the shared codec publishes.

**Why major.** `bitCodec` is the codec of every prong's security games and of T0–T2. Two consequences follow:
- The efficiency fill's machine `B` must reproduce `decodeBitMove` on **arbitrary** raw output of `A` (`Efficiency.lean:120–123`). The fill brief's rule 10 forbids unfolding it.
- So the fill needs a complete characterization of `decodeBitMove`. With the current `decodeIdx`, no characterization in the documented terms is true (the alias is a counterexample).

So the documentation is materially misleading, and the API the fill needs cannot be stated. That is major under the gate 02 guide. It is not a blocker, because no statement builds on wrong mathematics (see "Effect" below).

### Fix (recommended): strict unary decoding, with converses

```lean
/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length `≥ k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i   -- re-proved

/-- Converse: exactly the unary codes decode, each to its index. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true

/-- Every other word is rejected. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true

/-- Converse of `decodeBitMove_query`: only the canonical query word decodes as that query. -/
theorem decodeBitMove_eq_query_iff {w : List Bool} {i : Fin k} {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))

/-- **The default:** a word that is neither a canonical query nor a canonical output decodes to
`zeroBits dα`. With `decodeBitMove_query` and `decodeBitMove_ret` this covers every input. -/
theorem decodeBitMove_of_not_canonical {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα)
```

- **The proofs live in `BitCodec.lean`.** They may unfold that file's own `decodeIdx`/`decodeBitMove`. They also use:
  - the published `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:261`);
  - the new `decodeIdx_eq_some_iff`;
  - a converse for `decodeFin`: `decodeFin ℓ w = some x → w = List.ofFn x`. It does not exist yet.
- **The `decodeFin` converse** can be proved without unfolding `decodeFin`, about 8 lines:
  - `length_eq_of_decodeFin_eq_some` (`Adversary.lean:89`) gives `w.length = ℓ`;
  - rewrite `w` as `List.ofFn` of its own entries;
  - `decodeFin_ofFn` then gives `some f = some x`.

  Its home is `Asymptotic/Adversary.lean` (pack 03a), which is outside S2b's change set and is imported almost everywhere. Recommended: a `private` copy in `BitCodec.lean`, plus a requested shared lemma `decodeFin_eq_some_iff` for the next ch. 2–4 window.
- **Optional, and useful to the fill and to prong reductions:** a canonical encoder `encodeBitMove : Move (bitSpec din dout) (Fin dα → Bool) → List Bool`, with `decodeBitMove_encodeBitMove` and `encodeBitMove_injective`. The fill's `B` can then output `encodeBitMove (decodeBitMove w)`, which is the canonicalization step.
- **Docstrings.** `BitCodec.lean:59` gains "every other word is `none`". `:20–23` and `:73–75` can stay as they are, because after the fix they are true.

**Size:** about 60–90 lines in `BitCodec.lean` (the fix, 1 proof re-done, 4–5 lemmas, the private helper), plus about 25 lines if `encodeBitMove` is added.

### Effect on proofs

- **S2b.** Only `decodeIdx_replicate` (`:64–68`) changes. Its `dif_pos` needs the second conjunct, which is `List.length_replicate` plus `rfl`. `decodeBitMove_query`/`_ret` (`:109`, `:114`) go through unchanged: `simp` uses `decodeIdx_replicate`.
- **`Efficiency.lean`.** It contains no proof about the decoder. `InteractiveHandler.call` (`:182`) uses `decodeBitMove` in a definition. Its meaning changes only on handler outputs with a non-unary index, which now take the default.
- **Efficiency fill (not issued).**
  - The round function adds an all-`true` check on the index. It is polynomial-time by the pairing calculus.
  - The proof gets easier: it uses the converse lemmas instead of unfolding.
  - The brief draft's T0 status line ("T0, done and compiling") needs a refresh.
- **Prongs.** I grepped `wt-prong-{a,b,c,d}`, and also `wt-prong-d2`, `wt-pb-yao` and `wt-pb-compose`. No proof unfolds or reasons about `decodeIdx`, `decodeBitMove` or `bitCodec`. The uses are definitions only:
  - prong A: `Authentication/Defs.lean:122,197` (the forger codecs);
  - prong C: `Composability/{Defs:172, PublicKey:382, NonMalleable:71, SimNonMalleable:180,239}`.

  Nothing to re-prove.

### Does any statement change meaning?

No statement text changes. Only the meaning per machine changes: a machine that emits a non-unary index now gets the default return where it used to get a query.

Every notion built on `bitCodec` quantifies over all `A : NUPPT` (prongs A and C: forgery, IND, NM and SIM-NM games; T1 and T2). The class of computations `{A.toComp(On) (bitCodec …) n q r}` is the same before and after:
- **From the old decoder to the new:** post-compose `A` with the polynomial-time canonicalizer "replace a length-`i` index word by `1^i`".
- **From the new decoder to the old:** post-compose with "replace a non-unary query word by `pairEncode [true] (List.ofFn (zeroBits dα))`".

`Complexity.exists_comp` (`Closure.lean:200`) gives `B.coins = A.coins` and `B.runAtL n y r = post (A.runAtL n y r)`, so the coin space is identical and every advantage is preserved. This argument is not in Lean, and nothing needs it to be.

### Ruling: yes, light (R-04-1, §6)

`Efficiency.lean:21` declares the T0 definitions "final", and the fill brief freezes them at issue. The brief is not yet issued, so the change is cheap now.

---

## 2. F02 (major): missing defining equations; consumers unfold other files' definitions

### Verdict: **true, and understated**. Severity: **major (agree)**.

**Rule.** `policy.md` §1 says, under "Definitions land with their lemmas": "Every new public `def` is published, in the same PR and beside the definition, with the lemmas that let a consumer read it without unfolding … Consumers never unfold another file's definition." `briefs/pass-shelat-ch5-8/WORKFLOW.md` (rule 10) adds:
- it "applies to the maintainer's own API proofs too";
- only core and Mathlib definitions "may reduce in `rfl`, `decide` or `show`";
- "an API that must look inside an author's definitions goes beside them, in their file".

The fill brief repeats rule 10 for T1/T2. So without these equations the fill must either break the rule or copy definitions privately.

**The auditor's sites, all confirmed:**
- `Bridges/Machines.lean:65`: `simp only [MachineCodec.encodeLog, …, encodeHist]`. Also `:63`, `| nil => rfl` through both bodies.
- `:79`, `:82`: `unfold buildComp buildTree`.
- `:108`: `simp only [NUPPT.toComp, NUPPT.toOracleAdversary]`.
- `Bridges/Strategies.lean:183`: `simp only [Protocol.outP, Protocol.outV, Protocol.transcriptWith]`.

**Sites the auditor missed (S2b proofs reading other files' TCSlib definitions):**

| Site | What it reads | Kind |
|---|---|---|
| `Bridges/Experiments.lean:119` (`acceptProb_eq`) | `Games.accept` (`Advantage.lean:63`) | `rw [… accept …]` |
| `Bridges/Experiments.lean:127` (`distAdv_eq`) | `Games.advantage` (`Advantage.lean:67`) | `rw [distAdv_def, advantage, …]` |
| `Bridges/QueryTree.lean:76–77` (`simulate_ofComp_pure`) | `Games.simulate`, `QueryImpl.ofComp` (`Simulate.lean:74,115`), `OracleComp.bind` | `rfl`; `exact ih _` by defeq |
| `Bridges/QueryTree.lean:86–87` (`eval_eq_evalFn`) | `QueryTree.eval` (published `eval_ret`/`eval_query` exist but are not used) | `rfl`; defeq |
| `Bridges/QueryTree.lean:103–108` (`simulate_eq`) | `QueryTree.simulate` (`OracleAdversary.lean:150`, no equations), `QueryImpl.ofComp`, `OracleComp.call` | `rfl`, `show`, `simp only [… QueryImpl.ofComp …]` (:106) |
| `Bridges/Strategies.lean:138,142–145` (`exec_turnParty`) | `Party.exec`, `step`, `close`, `endWith`, `ExecOutcome.swap` (`Protocols.lean:101–146`), `OracleComp.bind` | `rfl`, `show` |
| `Bridges/Strategies.lean:159` (`exec_eq_alt`) | D8 `exec` at 0 (published `exec_zero` exists) | `rfl` |
| `Bridges/Strategies.lean:163` (`exec_eq_alt`) | `moverIsV` (`Interaction.lean:205`; `moverIsV_true`/`_false` exist) | `simp [moverIsV, h]` |
| `Hopping.lean:85,88,168` | `OracleComp.AllOutputs`, moved by S2b to `OracleComp.lean:268` | term-mode defeq (`exact h a hc`, `hc j`, `exact hs`) |
| `Protocols.lean:238,262,263,268` | `AllOutputs` on `.pure` | `show`; anonymous constructors |
| `Machines.lean:112,116–117` (`buildComp_costBoundedBy`) | `CostBoundedBy` (`OracleComp.lean:203`; `costBoundedBy_pure`/`_query` exist) | `exact trivial`; anonymous constructor |

So 16 S2b proofs read another file's definitions, against the 4 proofs (5 sites) the auditor named. Two cases are new debt rather than missing equations:
- **The `AllOutputs` move.** Gate 02 closed `AllOutputs` as `Hopping.lean`'s own definition. Moving it made `Hopping` and `Protocols` cross-file consumers of a predicate that has no `_iff` lemmas. Check 8 does not flag it, because `allOutputs_true` matches the name.
- **The `Bridges/QueryTree` and `Bridges/Experiments` reads** target S2a definitions (`Simulate.lean`, `Advantage.lean`) that gate 02 closed without equations. Their first cross-file consumers are S2b's.

### Equation lemmas to add, per definition

All are `rfl`, `Iff.rfl`, or a two-line `unfold`/`rw` in the definition's own file. None gets `@[simp]`. Each docstring states its formula (policy §1).

**S2b's own definitions**

| Definition (file:line) | Lemmas |
|---|---|
| `MachineCodec.encodeLog` (`Machines.lean:89`) | `encodeLog_nil : codec.encodeLog [] = []`; `encodeLog_cons : codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h)` |
| `buildComp` (`Machines.lean:97`) | four case lemmas covering every input: `buildComp_zero_of_ret (h : next hist = .ret a) : buildComp next t 0 hist = .pure a`; `buildComp_zero_of_query (h : next hist = .query i x) : … = .pure t`; `buildComp_succ_of_ret`; `buildComp_succ_of_query (h : next hist = .query i x) : buildComp next t (q+1) hist = .query i x fun y => buildComp next t q (hist ++ [⟨i, x, y⟩])` |
| `NUPPT.toComp` (`Machines.lean:122`) | `toComp_eq : D.toComp codec n q r = buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []` |
| `NUPPT.toCompOn` (`Machines.lean:135`) | `toCompOn_eq` (the same, with `pairEncode x (codec.encodeLog hist)`) |
| `bitSpec` (`BitCodec.lean:56`, abbrev) | `bitSpec_dom`, `bitSpec_rng` (a new public abbrev still lands with an `_eq` lemma, policy §1) |
| `decodeIdx`, `decodeBitMove` | the converses of §1 |
| `zeroBits` (`BitCodec.lean:71`) | `zeroBits_apply : zeroBits d j = false`; `ofFn_zeroBits : List.ofFn (zeroBits d) = List.replicate d false` |
| `bitCodec` (`BitCodec.lean:97`, structure-valued) | `@[simps (config := { isSimp := false }) decodeMove encodeEntry timeout]`, which gives `bitCodec_decodeMove`, `bitCodec_encodeEntry` and `bitCodec_timeout`; plus `encodeLog_bitCodec`, saying the log encoding does not depend on `dα` (`InteractiveHandler.call` encodes logs with `dα = 0`, `Efficiency.lean:184`, while T2's `B` uses `dα.eval n`) |
| `bitSpecAt` (`Efficiency.lean:62`, abbrev) | `bitSpecAt_eq` |
| `PolyHandler.input` (`:86`) | `PolyHandler.input_eq` |
| `PolyHandler.answer` (`:93`) | `answer_of_pairDecode_eq_none`, `answer_of_pairDecode_eq_some` (together, every input), and the well-formed case `answer_of_run_eq (h : H.run (input …) = pairEncode (List.ofFn y) (List.ofFn s')) : H.answer … = (y, s')` |
| `PolyHandler.impl` (`:105`) | `PolyHandler.impl_apply : H.impl n z ω i x s = .pure (H.answer n z ω s i x)` |
| `InteractiveHandler.input` (`:171`) | `InteractiveHandler.input_eq` |
| `InteractiveHandler.call` (`:178`) | `call_eq` (`= buildComp (…) (zeroBits _) (H.perCall.eval n) []`) |
| `InteractiveHandler.impl` (`:190`) | `InteractiveHandler.impl_apply` |
| `singleCodec` (`Bridges/Machines.lean:45`) | `@[simps (config := { isSimp := false }) decodeMove encodeEntry timeout]` |
| `toHist` (`Bridges/Machines.lean:54`) | `toHist_nil`, `toHist_cons` |
| `OracleComp.evalFn` (`Bridges/QueryTree.lean:64`) | `evalFn_pure`, `evalFn_query` |
| `treeImpl` (`Bridges/QueryTree.lean:91`) | `treeImpl_apply` |
| `acceptGame` (`Bridges/Experiments.lean:107`) | `acceptGame_eq` |
| `turnParty` (`Bridges/Strategies.lean:69`) | `turnParty_zero : turnParty next 0 M = .pure (next M)` (`turnParty_succ` exists) |
| `waitParty` (`:80`) | `waitParty_none`, `waitParty_some_zero`, `waitParty_some_succ : waitParty next (k+1) M (some y) = turnParty next k (M ++ [y])` |
| `alt` (`:95`) | `alt_zero`, `alt_succ : alt nF nG (k+1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap` (`alt_succ_last` is a derived law, not the defining equation) |
| `OracleComp.AllOutputs` (`OracleComp.lean:268`, moved) | `allOutputs_pure : (OracleComp.pure a).AllOutputs P ↔ P a`; `allOutputs_query : (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P` |
| `singleSpec` (`OracleComp.lean:155`, abbrev) | `singleSpec_dom`, `singleSpec_rng` (optional) |
| `QueryTree.induct` (`OracleAdversary.lean:97`, new; motive in `Sort`) | `induct_ret`, `induct_query` (its computation rules; needed only if data is defined with it) |

**Definitions in files S2b already changes, which S2b's proofs consume (predating the rule, "covered as consumers need them")**

| Definition (file:line) | Lemmas | Consumer |
|---|---|---|
| `encodeHist` (`Asymptotic/PRF.lean:201`) | `encodeHist_nil`, `encodeHist_cons` | `Bridges/Machines.lean:63–67` |
| `buildTree` (`PRF.lean:208`) | the four case lemmas, as for `buildComp` | `Bridges/Machines.lean:79–84` |
| `NUPPT.toOracleAdversary` (`PRF.lean:235`) | `toOracleAdversary_eq` | `Bridges/Machines.lean:108` |
| `QueryTree.simulate` (`OracleAdversary.lean:150`) | `simulate_ret`, `simulate_query` | `Bridges/QueryTree.lean:103–108` |
| `oracleDist` (`OracleAdversary.lean:191`) | `oracleDist_apply` (optional now; the ch. 2–4 files unfold it widely, pack 03d) | — |
| `Party.step`, `close`, `endWith`, `ExecOutcome.swap` (`Protocols.lean:101–126`, S2a) | `step_pure`, `step_send` (`.query (.inl ()) m k`), `step_coin` (`.query (.inr j) x k`); `close_pure`, `close_send`, `close_coin`; `endWith_eq`; `swap_done`, `swap_outOfFuel`, `swap_sentAfterEnd` | `Bridges/Strategies.lean:138–145` |

**Definitions in files outside S2b's change set (R-04-2 decides whether they join it)**

| Definition (file:line) | Lemmas | Consumer |
|---|---|---|
| `Games.accept`, `Games.advantage` (`Games/Advantage.lean:63,67`, S2a) | `accept_eq`, `advantage_eq` (and `guessGame_eq`, which check 8 also lists) | `Bridges/Experiments.lean:119,127` |
| `QueryImpl.ofComp` (`Games/Simulate.lean:115`, S2a) | `ofComp_apply : QueryImpl.ofComp f i x s = (f i x).bind fun y => .pure (y, s)`. Prong A will want `withLog_apply` for its MAC game, `Authentication/Defs.lean:130`. Check 8 also lists `passthrough`, `sum` and `QueryImpl.comp`. | `Bridges/QueryTree.lean:76,106` |
| `Protocol.transcriptWith`, `transcript`, `outV`, `outP`, `viewV`, `viewP`, `Strategy.out` (`ZeroKnowledge/Interaction.lean:326,331,340,344,349,354,267`, ch. 2–4, pack 03e) | `transcriptWith_eq` (`= exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)`); `transcript_eq_transcriptWith` (the name `transcript_eq` is taken); `outV_eq` (for any `P'`; `outV_eq_out` covers only the honest `π.P`); `outP_eq`; `viewV_eq`, `viewP_eq`; `Strategy.out_eq` | `Bridges/Strategies.lean:183`; prong B (below) |

### Consumer proofs to re-point (S2b)

1. `Bridges/Machines.lean`:
   - `encodeLog_singleCodec` (`:62–67`): use `encodeLog_nil/cons`, `encodeHist_nil/cons`, `toHist_cons` and `singleCodec_encodeEntry`;
   - `buildComp_singleCodec` (`:78–90`): use the `buildComp`/`buildTree` case lemmas;
   - `toComp_singleCodec` (`:98–110`): use `toComp_eq`, `toOracleAdversary_eq` and `singleCodec_decodeMove`.
2. `Bridges/QueryTree.lean`:
   - `simulate_ofComp_pure` (`:76–77`): use `simulate_pure/query`, `ofComp_apply`, `pure_bind` and `evalFn_*`;
   - `eval_eq_evalFn` (`:86–87`): use `eval_ret/query` and `evalFn_*`;
   - `simulate_eq` (`:103–108`): use `QueryTree.simulate_ret/query`, `treeImpl_apply`, `ofComp_apply` and `call_bind`.
3. `Bridges/Experiments.lean`: `acceptProb_eq` (`:119`) and `distAdv_eq` (`:127`) use `accept_eq` and `advantage_eq`.
4. `Bridges/Strategies.lean`:
   - `exec_turnParty` (`:138–145`): use `Party.exec_zero/succ`, the `step/close/endWith/swap` lemmas, `turnParty_zero`, `waitParty_*` and `pure_bind`;
   - `exec_eq_alt` (`:159`, `:163`): use `exec_zero`, `alt_zero` and `moverIsV_true/false`;
   - `exec_strategies` (`:183`): use `outP_eq`, `outV_eq` and `transcriptWith_eq`.
5. `Machines.lean`: `buildComp_costBoundedBy` (`:112`, `:116–117`) uses `costBoundedBy_pure` and `(costBoundedBy_query …).2`.
6. `Hopping.lean`: `expect_mono_of_allOutputs` (`:85`, `:88`) and `simulate_allOutputs_bad` (`:168`) use `allOutputs_pure/query`.
7. `Protocols.lean`:
   - `endWithT_ne_outOfFuel` (`:238–239`): use `allOutputs_pure`, and `Option.elim_none`/`Option.elim_some` instead of `simp [Option.elim]` (N5);
   - `execT_trace` (`:262–268`): use `allOutputs_pure.2 ⟨…⟩`.

That is 16 proofs (3 + 3 + 2 + 3 + 1 + 2 + 2) and about 60–80 changed lines.

### Size

| Part | Lemmas | Lines (with docstrings) |
|---|---|---|
| `Machines`, `BitCodec` (with F01), `Efficiency` | about 30 | about 200–240 |
| `Bridges/*` | about 17 | about 80 |
| `OracleComp`, `Protocols`, `OracleAdversary`, `PRF` (in the change set) | about 25 | about 120 |
| `Advantage`, `Simulate`, `Interaction` (outside) | about 10–15 | about 50–70 |
| **Total** | **about 75–85** | **about 450–510**, plus about 70 lines re-pointed |

About one maintainer day.

**Evidence to redo:**
- the replay of `Games/*`;
- the downstream of `PRF.lean`, `OracleAdversary.lean`, `Protocols.lean` and `OracleComp.lean`, which is already S2b's set;
- under R-04-2 option 1, also the downstream of `Advantage.lean`, `Simulate.lean` and `Interaction.lean` (the ZK modules);
- the axiom prints;
- check 8 (§5, N2);
- a rule-10 seal over the 16 re-pointed proofs.

### Effect on the prongs

- **Statements:** none. All additions are lemmas.
- **Prong B proofs** that read ch. 2–4's D8 definitions, re-pointable once the `Interaction.lean` lemmas land (9 sites):
  - `ObliviousTransfer.lean:155,211`: `simp [Protocol.outV, Protocol.transcriptWith, otProtocol, exec, …]`;
  - `ComposePhases.lean:530,542`: `show` through `viewP`/`viewV`;
  - `ComposePhases.lean:558,577`: `show` through `outP`/`outV`/`transcriptWith`;
  - `Yao.lean:548,555`: `yaoMain_outV/outP … := rfl`;
  - `Yao.lean:795,798`: `show (yaoMain …).outV/outP …`.
- **Prong B's own requested lemmas.** The Yao worker reported these. They are `private … := rfl` copies of another file's definition in `Yao.lean`, so they are themselves definitional closures. They should become shared lemmas beside their definitions, and the copies should be deleted:
  - `keyAt` (`Garbling.lean:192`): `keyAt_of_lt` and `keyAt_of_not_lt`, replacing `keyAt_eq'` (`Yao.lean:310`);
  - `garbledValues` (`Garbling.lean:236`): `garbledValues_eq`, replacing `garbledValues_eq'` (`Yao.lean:610`). Its only lemma, `garbledValues_getD`, is a correctness claim, not an equation.
  - `inputKeys` (`Garbling.lean:231`): `inputKeys_eq`, replacing `inputKeys_eq'` (`Yao.lean:615`);
  - `tableAt` (`Garbling.lean:213`): `tableAt_of_not`, the off-gate case, replacing `tableAt_eq'` (`Yao.lean:620`). `tableAt_gate` already exists.
  - `HybridProtocol.answersB` (`Hybrid.lean:91`): `answersB_eq`, which removes the `show` at `Yao.lean:738–739`.

  This is prong B's work for gate 06, not S2b's. Check 8 on prong B also lists 40 more of its definitions, among them `Garbling.lean`'s `argKeys`, `evalGate`, `garbledRow` and `garbledTable`.
- **Prongs A, C, D:** no current proof reads an S2b definition; their reductions are still sketches. The future fills of Thms 135.4, 137.2, 144.1 (prong A) and 168.2, 170.4, 175.9 (prong C) will need:
  - `toComp_eq`/`toCompOn_eq`;
  - the `buildComp` cases;
  - `bitCodec_*`, `encodeLog_cons` and `zeroBits_apply`;
  - `ofComp_apply`/`withLog_apply`.

  Prong C already states lemmas whose right-hand sides are `.pure (zeroBits _, s)` (`Composability/Defs.lean:156,162`; `PublicKey.lean:371,377`; `NonMalleable.lean:115`; `SimNonMalleable.lean:173`).

### Ruling: scope only (R-04-2, §6)

The rule is binding, so there is no "whether". The ruling decides whether the S2a and ch. 2–4 lemmas join this PR.

---

## 3. Minors

### F03: `PolyHandler.answer` defaults componentwise

- **Verdict: true. Severity: minor (agree).**
- **Evidence:**
  - `Efficiency.lean:91–92`: "A malformed output gives the all-`false` answer and state".
  - `:97–100`: after `pairDecode` succeeds, the code is `((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`. So `pairEncode [true] []` (with both lengths 1) gives answer `true` and state all-`false`.
- **Missed by the auditor (N6).** T2's handler defaults **jointly**. `InteractiveHandler.call` decodes `y ‖ s'` with one `decodeFin (dout + stateLen)` through `decodeBitMove` (`:182`), so a wrong total length gives all-`false` for both. T1 and T2 thus disagree on malformed output, and neither docstring says so.
- **Fix (recommended, docstring-only).** Reword `:91–92` to: "if `run`'s output is not a pair, both are all-`false`; otherwise each component of the wrong length is replaced by all-`false` independently". Add the `answer_*` equations of §2. State the joint default in `InteractiveHandler`'s docstring (`:145–150`).
- **Alternative (not recommended now).** Reject the whole pair, aligning with T2. That changes a T0 definition and would need a ruling. No consumer cares: handlers are the reduction's own code and never emit malformed output.
- **Effect on prongs:** none (no prong defines a handler yet).
- **Ruling:** no.

### F04: "up to `perCall(n)` rounds of `run`"

- **Verdict: true. Severity: minor (agree).**
- **Evidence.** `Efficiency.lean:146–147` says "One inner query `x` to oracle `i` is answered in up to `perCall(n)` rounds of `run`". But `call` is `buildComp … (H.perCall.eval n) []` (`:182–185`), and `buildComp` inspects one more move at fuel 0 (`Machines.lean:99–101`). So `p` outer queries take up to `p + 1` activations, and `perCall = 0` still gives one activation. `call`'s docstring "up to `perCall(n)` rounds against the outer oracles" (`:175–176`) is ambiguous. The field docstring (`:157`, "bound on outer queries") and the module doc (`:37`, "up to `perCall(n)` times per inner query") are correct.
- **Fix (docstring-only).** `:146–147`: "answered with at most `perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run` (the last returns the answer or, with the budget spent, is cut off with the default)". The same for `:175–176`. The fill brief's replay bound should count `q(n)·(perCall(n)+1)` handler activations, which the auditor's construction outline already does.
- **Effect:** none on statements. T2's budget `q(n)·perCall(n)` counts queries and is correct.
- **Ruling:** no.

### F05: attestation 3 miscounts the axiom log

- **Verdict: true. Severity: minor (agree).**
- **Evidence.**
  - `evidence/axioms.log` has 237 entries, including `uprob_update_absorb'` (`:226`). Two contain `sorryAx` (T1 `:154`, T2), so 235 are clean. The pack says 236 and 234.
  - A comment-stripped count of the 22 changed files gives 237 public and 14 private theorem declarations (251 in all), matching the auditor.
  - The private ones cannot be `#print`ed from outside their file. Their admission-freeness is attested instead by the replay's per-module `sorry=` counts (`replay.log:732`, `Games/Efficiency … sorry=2`, all other S2b modules `sorry=0`).
- **Fix.** Reword attestation 3: "237 public theorems printed; 235 standard-only; T1 and T2 `sorryAx`. The 14 private theorems are covered by the replay's admission counts." When the evidence is refreshed (§7), also carry the source/olean provenance the auditor asks for. The replay header names `827ad8e1`, while the axioms and lint name `afe5982f`.
- **Effect on prongs:** none.
- **Ruling:** no.

### F06: inherited descriptions overstate their statements

**Verdict: true, all five points checked. Severity: minor (agree).** None is an F-1 regression: F-1's diff to these files touches only universe binders.

| Point | Evidence | Fix (docstring-only) |
|---|---|---|
| `multiMsgAdv_boundedBy` | `MultiMessage.lean:147–148`: "makes exactly `q + 1` queries"; the statement is `BoundedBy (q + 1)` | "at most `q + 1`" |
| `decodeFin_runAt_prfDec_of_not_wf` | `:467–468`: "a ciphertext `w` that is not a pair of `n`-bit strings"; the premise is the projected lengths, and `w = []` at `n = 0` is not a pair but meets them | "whose two projections are not both `n` bits long" |
| `pairFstD_pairFstD_histBlock` | `MultiMessageLemmas.lean:299`: "the two components … the query and the answer"; the statement gives the query only | "the query component" (or add the answer projection) |
| `take_drop_ofFn_blocks` | `:377–379`: "(private copy …)" but public. It is also an unledgered duplicate (N4). | see N4 |
| `exists_queryChain_nuppt` | `:618–619`: "asks `ρ₀, …, ρ_{q(n)}`"; the statement gives evaluation equality only | "whose evaluation against any oracle `g` is …" |
| `SubHybrids.tableDist`, `GGM.ggmDist` | `SubHybrids.lean:103`, `GGM.lean:194`: "*Cost.* … at most `q` evaluations of `G`" holds only when `A.BoundedBy q` | add "for `A` bounded by `q`" |

- **Where to fix.** The files are in S2b's change set (F-1), but their packs are 03d (`MultiMessage`) and 03j (`MultiMessageLemmas`), both pending. Recommended: fix the docstrings in S2b and tell the 03d and 03j pack authors, so those auditors do not re-raise them.
- **Effect on prongs:** none.
- **Ruling:** no.

---

## 4. Severities at a glance

| # | Verdict | Auditor | Proposed | Fix kind | Ruling |
|---|---|---|---|---|---|
| F01 | true | major | major | definition change plus new lemmas | R-04-1 (light) |
| F02 | true, understated | major | major | new lemmas, 16 proofs re-pointed | R-04-2 (scope) |
| F03 | true | minor | minor | docstring plus equations | no |
| F04 | true | minor | minor | docstring | no |
| F05 | true | minor | minor | evidence wording | no |
| F06 | true | minor | minor | docstrings | no |
| N1 | missed | — | **major** | statement change before the fill (or wrappers) | R-04-3 |
| N2 | missed | — | minor | evidence (lint and seal) | no |
| N3 | missed | — | minor | docstring | no |
| N4 | missed | — | minor | ledger entry | no (ledger) |
| N5 | missed | — | minor | proof (folded into F02) | no |
| N6 | missed | — | minor | folded into F03 | no |
| N7 | missed | — | minor | evidence (folded into N2) | no |

---

## 5. What the auditor missed

### N1 (proposed major): T1/T2 do not cover the reductions they are cited for

The auditor's "Exact limitations" 1–4 (findings lines 179–186) are correct, but were not counted ("possible missing future prongs are not counted as additional present majors"). The brief's item 3 asks exactly this question ("T1 and T2 must be usable contracts … what a reduction needs"). The coverage is already claimed in two places:
- `Efficiency.lean:44–47`: T2 is what "the PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions" need;
- the pack: T2 is "needed by the reductions of Thms 135.4, 144.1, 168.2, 170.4".

The prongs' sketches build on that claim. Five gaps:

1. **No adversary input.** T1 and T2 simulate `A.toComp` (`Efficiency.lean:136`, `:224`). The signature and public-key games run `A.toCompOn … pk`:
   - prong A: `Authentication/Defs.lean:207`;
   - prong C: `Composability/PublicKey.lean:391`, `NonMalleable.lean:100`, `SimNonMalleable.lean:218,260`.

   In a reduction the input is computed from the reduction's input `z` and seed `ω`. Lamport builds `pk` from `y` and its coins; hash-and-sign's `B` and `C` build `⟨pk, i⟩`.
2. **No final state and no finalization.** T1 hides the state (`∃ s`) and T2 projects it away (`res.1`). Several reductions post-process `A`'s output with the state or seed, and sometimes with more oracle queries:
   - the PRF MAC's distinguisher queries at `A`'s message and checks freshness against the log;
   - Lamport outputs `σ'_i` or aborts;
   - hash-and-sign outputs `(m, m′)` or `(h_i(m′), σ′)`;
   - Thm 175.9 (⇒) asks ℓ more `Dec` queries and runs `D`;
   - `padded_cpa` flips or zeroes the guess.
3. **Normalized output only.** T1 gives `padFin dα (B.runAt …)` (`:138`). An inverter is read through `decodeFin` (`NUPPT.inverter`, `Adversary.lean`), so Lamport's `B` needs exact output.
4. **No bridge to the PRF assumption.** `PRF F` (via `OracleEnsemble.Indist`) quantifies over `D.toOracleAdversary`, which is `D.toComp (singleCodec ℓ₁ ℓ₂)` by `toComp_singleCodec`. T2's `B` is a `toCompOn (bitCodec …) z` machine. The two differ in:
   - the index type (`Unit` against `Fin 1`);
   - the query word (`⟨[false], x⟩` against `⟨[false], ⟨[], x⟩⟩`);
   - the verdict word (`[true, b]` against `⟨[true], [b]⟩`);
   - the log entry (`⟨x, y⟩` against `⟨[], ⟨x, y⟩⟩`);
   - the input (none against `⟨z, log⟩`).

   No lemma relates them. Every PRF-based reduction needs one: 135.4, 168.2 and 170.4.
5. **T1 is cited where only T2 can apply.** T1's handler targets `unifSpec` and answers with `.pure` (`:105–108`), so it cannot query any oracle. Yet "by T1" is cited for oracle-forwarding reductions:
   - `PRFMAC.lean:111` ("the handler forwarding queries");
   - `PRFScheme.lean:76` ("querying its own oracle … efficiency by T1");
   - `CCA2Scheme.lean:300` ("answers `Enc′` and `Dec′` with its oracle … by T1");
   - `NonMalleable.lean:125` ("asks CCA2's `Dec` … `D` is run by T1's handler").

**What each reduction needs:**

| Reduction (prong, file:line) | Cites | Input | Final/state | Exact output | Codec bridge | Oracle (T2) |
|---|---|---|---|---|---|---|
| Thm 135.4 PRF MAC (A, `PRFMAC.lean:111`) | T1 | — | yes (final query, log) | — | yes | yes |
| Thm 137.2 Lamport (A, `Lamport.lean:463–464`) | T1 | yes | yes (abort, `σ'_i`) | yes (inverter) | — | — |
| Thm 144.1, `B` (A, `HashAndSign.lean:266–267`) | T1 | yes | yes | — | — | — |
| Thm 144.1, `C` (A, `HashAndSign.lean:271–272`) | T2 | yes | yes (`h_i(m′)`) | — | — | yes |
| Thm 168.2 CPA/CCA1 (C, `PRFScheme.lean:76`) | T1 | — | — (`b` fixed in the handler) | — | yes | yes |
| Thm 170.4 (C, `CCA2Scheme.lean:300`) | T1 | — | — | — | yes | yes |
| Thm 175.9 (⇒) (C, `NonMalleable.lean:125`) | T1 | yes | yes (ℓ `Dec` queries, then `D`) | — | — | yes |
| `padded_cpa` (C, `PublicKey.lean:417`) | T1 | yes | yes (flip or zero) | — | — | — |

**Why major.** The coverage claim at `Efficiency.lean:44–47` is materially misleading. T0–T2 freeze at the fill's issue (fill brief, ground rule 1). A later change costs a re-freeze and a re-fill, or one machine construction per reduction (several hundred lines each, by the S2b-efficiency note's own count for ch. 2–4). No present statement is wrong (T1/T2 are true candidates), so it is not a blocker.

**Fix (recommended, R-04-3 option 1): extend before issue.** A sketch:

```lean
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  stateLen seedLen : PolyExpr
  init : ∀ n, Fin (stateLen.eval n) → Bool
  run : List Bool → List Bool
  poly : PolyTimeComputable run
  /-- The adversary's input, from `⟨1^n, ⟨z, ω⟩⟩`. -/
  advIn : List Bool → List Bool
  advIn_poly : PolyTimeComputable advIn
  /-- The reduction's output, from `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (final state, adversary's output). -/
  out : List Bool → List Bool
  out_poly : PolyTimeComputable out

-- T1': exact output, adversary with input
∃ B : NUPPT, ∀ n, ∃ φ, ∀ z ω r, ∃ a s,
  simulate (H.impl n z ω) (A.toCompOn codec n (q.eval n) (H.advIn (seedIn n z ω)) r) (H.init n)
    = .pure (a, s) ∧
  B.runAt n z (φ (ω, r)) = H.out (pairEncode (seedIn n z ω) (pairEncode (List.ofFn s) (List.ofFn a)))
```

- **T2'** uses the same fields, with an interactive finalization: one more `call`-like phase `H.finish n z ω s a` on the outer oracles, with budget `finCall` and a `dβ`-bit output. Its conclusion is `(simulate …).bind (fun res => H.finish n z ω res.2 res.1) = B.toCompOn (bitCodec din' dout' dβ) n (q·perCall + finCall) z (φ (ω, r))`.
- **Two companions:**
  - `exists_toCompOn_of_toComp`: an input-free adversary is an input-taking one that ignores its input. It follows from `exists_comp` with `pre = pairSndD`; the coins are unchanged.
  - **T4**, the codec bridge: `∀ B, ∃ B'` with `B'.coins = B.coins` such that `(B'.toOracleAdversary n ℓ₁ ℓ₂ q r).eval f` equals the evaluation of `B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1) n q [] r` against `fun _ => f`, read at bit 0. An eval-level equality suffices for `oracleDist`/`prfAdv` and avoids relabelling `Unit` against `Fin 1`.
- **Cost.** T0 gains 4 fields per handler structure and one definition. T1/T2 are restated (still `sorry`), and T4 and the companion are stated. The fill grows by an estimated 400–700 lines (input threading, finalization replay, T4's re-encoding of logs). The prong sketches above re-cite T1′/T2′/T4. No prong statement text changes.

**Effect on the prongs.** Docstring sketches only, at the eight sites listed. Their theorems are `sorry` under sketches.

### N2 (minor): the lint attestation omits check 8; no rule-10 seal evidence (with N7)

- **What the pack ran.** Attestation 4 (`evidence/lint.log`: "0 findings in 22 files") ran `scripts/style_lint.py`. That is main's per-file linter, with checks for docstrings, sketches, headers and size, but no check 8. `workflow.md` §6 names `scripts/campaign_style_lint.py` as the campaign lint, and says of check 8: "a landing adds no name to it".
- **What check 8 shows** (`--check8b`, `TCSlib/Cryptography`), at `a3c5fa8b` against `afe5982f`. S2b removes `invProb`, `predProb` and `uexp` (F-3, done) and **adds 16 names**:
  - `BitCodec`: `bitCodec`, `zeroBits`;
  - `Bridges/Experiments`: `acceptGame`;
  - `Bridges/Machines`: `singleCodec`, `toHist`;
  - `Bridges/QueryTree`: `OracleComp.evalFn`, `treeImpl`;
  - `Bridges/Strategies`: `waitParty`;
  - `Efficiency`: `answer`, `call`, `impl` ×2, `input` ×2;
  - `Machines`: `encodeLog`;
  - `OracleAdversary`: `induct`.
- **Name-only passes.** Check 8 accepts any lemma whose name starts with the definition's, so 8 more definitions pass on a name alone:
  - `buildComp` (`buildComp_costBoundedBy`);
  - `NUPPT.toComp` and `toCompOn` (`_costBoundedBy`);
  - `decodeIdx` (`decodeIdx_replicate`);
  - `decodeBitMove` (`_query`/`_ret`);
  - `turnParty` (`turnParty_succ`);
  - `alt` (`alt_succ_last`);
  - `AllOutputs` (`allOutputs_true`).

  This is F02's list in mechanical form.
- **Fix.** Re-run attestation 4 with `campaign_style_lint.py --check8b`. Its check-8 diff against the base should list no new name after F02. Add a rule-10 seal log (WORKFLOW rule 10: `attribute [local irreducible]` on every consumed definition, with controls) for the 16 re-pointed proofs.

### N3 (minor): `Bridges/Strategies.lean` promises results that are not there

- `:50–51` says: "The traced and probabilistic forms (views, and tapes sampled first) are stated in a later part of this file." The file ends at `exec_strategies` (`:173–189`).
- B4's design theorems 2–4 (traces, probabilities, fuel; `design/B4-strategy-embedding.md`) are not stated. The auditor noted that they are absent, but not that the docstring claims them.
- Fix: "are planned (B4 design note, theorems 2–4) and not yet stated". No prong uses B4 yet (grep for `turnParty`, `exec_strategies` and `Bridge.` in all prongs: none).

### N4 (minor, inherited): an unledgered duplicate

- `MultiMessageLemmas.lean:379`, `TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks`, has the same statement as `EnsemblesLemmas.lean:385`, `TCSlib.Cryptography.EnsembleLemmas.take_drop_ofFn_blocks`. Its docstring calls it a "private copy", but it is public.
- It is not in `duplication-ledger.md` (DL-1 to DL-8). It predates S2b.
- Policy §1, "Duplication": "every instance … must be human-approved".
- Fix: ledger entry DL-9 (keep the `EnsembleLemmas` copy and point `MultiMessageLemmas` at it), routed to pack 03j. Correct the docstring now (F06).

### N5 (minor): a core definition passed to `simp`

- `Protocols.lean:239`: `cases p.1 <;> simp [Option.elim]`. The 2026-10-23 rule allows core definitions only in `rfl`/`decide`/`show`.
- Fix: `Option.elim_none`/`Option.elim_some` (core lemmas). This is folded into F02's re-point 7.

### N6 (minor): T1's and T2's malformed-output defaults disagree

Folded into F03.

### Not findings (checked)

- **No new `@[simp]`.** The diff `a3c5fa8b..afe5982f` adds none.
- **The facades are complete.** `Games/Bridges.lean` imports all seven S2b modules, and `TCSlib.lean:60–61` imports `Games` and `Games.Bridges`. The facade's contents line for `Efficiency` names only T1; the auditor's editorial note stands, and the fix is to add T2.
- **The replay covers T2.** `replay.log:732` shows `Games/Efficiency … sorry=2`, recorded after the T2 commits, despite the `827ad8e1` header.

---

## 6. Rulings for the user (multiple choice; recommended option first)

**R-04-1 (F01): the unary index of the shared codec.**
1. **Strict unary decoding, with converse lemmas (recommended).** `decodeIdx` checks `iw = List.replicate iw.length true`. Add `decodeIdx_eq_some_iff`, `decodeIdx_eq_none_iff`, `decodeBitMove_eq_query_iff` and `decodeBitMove_of_not_canonical`, plus optionally `encodeBitMove`.
   - *Cost:* about 60–90 lines in `BitCodec.lean`, one lemma re-proved, and a T0 change before the fill is issued.
   - No prong edits; no change of meaning for any ∀-adversary notion.
   - The fill adds one all-`true` check.
2. **Keep length-only decoding, and document it.** The grammar becomes "any word of length `i < k` names oracle `i`", with converse `decodeIdx k iw = some i ↔ iw.length = i`.
   - *Cost:* docstrings at `BitCodec.lean:20–24,59,73–75` and `Efficiency.lean:149`.
   - The codec is no longer injective on accepted words.
   - It departs from D7's strict-format convention, under which ch. 2–4's `decodeOracleMove` is exact.

**R-04-2 (F02): the scope of the equation lemmas in this PR.**
1. **Everything S2b's proofs consume, in this PR (recommended).**
   - S2b's own definitions;
   - `PRF.lean`, `OracleAdversary.lean`, `Protocols.lean` (S2a definitions) and `OracleComp.lean`, already in the change set;
   - `Advantage.lean`, `Simulate.lean` (S2a) and `Interaction.lean` (ch. 2–4), which join it;
   - all 16 proofs re-pointed.

   *Cost:* about 75–85 lemmas, about 450–510 lines, about 70 lines re-pointed, and the replay extended to `Interaction.lean`'s downstream. Packs 03d and 03e get small additive deltas (`rfl` lemmas only). Prong B can then re-point its 9 D8 sites.
2. **S2b's own definitions and the files already in the change set now; `Advantage`, `Simulate` and `Interaction` in a follow-up PR before gate 06.**
   - *Cost:* `acceptProb_eq`, `distAdv_eq`, `simulate_ofComp_pure`, `simulate_eq` and `exec_strategies` keep reading those definitions until then. That is a recorded debt line the user acknowledges, and `Bridges/{Experiments, QueryTree, Strategies}` must be re-pointed twice.
3. **Acknowledge the whole debt and close.**
   - *Cost:* not recommended. The efficiency fill must then break rule 10 or carry private copies (each a disclosed duplicate), and every prong reduction repeats this.

**R-04-3 (N1): T1/T2 as contracts for the cited reductions.**
1. **Extend T0–T2 before the fill brief is issued (recommended).**
   - adversary input from a polynomial-time function of `⟨1^n, z, ω⟩` (`A.toCompOn`);
   - a polynomial-time finalization on (final state, output), interactive in T2 with its own budget;
   - exact output in T1;
   - companions `exists_toCompOn_of_toComp` and T4 (the codec bridge to `toOracleAdversary`).

   *Cost:* T0 gains 4 fields per handler and one definition; T1/T2 are restated (still `sorry`); 2 statements are added; the fill grows by about 400–700 lines; a delta re-audit of `Efficiency.lean`. The eight prong sketches are re-cited.
2. **Keep T1/T2 and add wrapper targets T4 (codec bridge), T5 (adversary input) and T6 (finalization and exact output).**
   - *Cost:* three more machine-level statements, each with its own functional equation by induction on the budget, plus composition of machines. More total work than option 1, and every reduction composes three or four results.
3. **Accept as a scope limitation.** Correct `Efficiency.lean:44–47` and the eight sketches to say what T1/T2 do not cover.
   - *Cost:* prongs A and C build their own machines for Thms 135.4, 137.2, 144.1 (×2), 175.9 and `padded_cpa`, and a PRF codec bridge for 135.4, 168.2 and 170.4. That is several hundred lines each: the per-reduction cost the efficiency route was meant to remove.

---

## 7. Proposed closing condition for gate 04

1. **F01** applied per R-04-1: the converse lemmas, and `decodeBitMove_of_not_canonical` proved.
2. **F02** applied per R-04-2: the lemmas of §2, and the 16 proofs re-pointed.
3. **R-04-3** ruled. Under option 1, T0–T2 restated and T4 stated before the fill brief is issued.
4. **F03, F04, F06, N3** docstrings fixed. N4 recorded in the ledger as DL-9 (pack 03j).
5. **Evidence refreshed at the new head:**
   - the replay, with source and olean provenance;
   - axiom prints with corrected counts (F05);
   - `campaign_style_lint.py --check8b` with no new check-8 name against the base (N2);
   - a rule-10 seal log for the re-pointed proofs (N2, N7).
6. **A delta re-audit** of `BitCodec.lean`, `Efficiency.lean` and the new equation lemmas. The equation lemmas are `rfl`, so a statement-only check suffices.

## ===== duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | The `j`-th block of `c` bits of a coin string, `(r.drop (j * c)).take c`, stated three times: `coinSlice` (`ZeroKnowledge/GraphIsomorphism.lean`, ch. 2–4), `Authentication.coinBlock` (`Authentication/Lamport.lean`, prong A), `Protocol.phaseSlice` (`Composability/SequentialZK.lean`, prong C) | found by the Lamport worker and the maintainer | Before the ch. 5–8 statement gate: one copy in a shared upstream module, with its length lemma, used by all three. |
| DL-7 | `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`: `Authentication.ofFn_padFin_of_length` (`Lamport.lean`) is the equal-length case of ch. 2–4's `ofFn_padFin_of_le` (`Asymptotic/Collections.lean`); `Composability.length_eval_of_length` (`CCA2Scheme.lean`) repeats the step inline | found by the Lamport worker | Before the ch. 5–8 statement gate: use `ofFn_padFin_of_le (le_of_eq h)`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, six copies plus an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`; with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; scheduled (G3-5) | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, private copies in `Collections.lean` and `GGMReductionEval.lean`, and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | accepted; scheduled (R-03l-1: clean up in gate 03's PR) | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | accepted; scheduled (R-03l-1) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | noted | Rename or merge in the same PR. |

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
  rw [acceptProb_def, acceptProb_def,
    uprob_prod_comm (fun R (r : ρ) => oracleDist A ((OracleEnsemble.random ℓ₁ ℓ₂).O n R) r = true),
    uprob_prod_comm (fun W (r : ρ) => lazyDist A (extendStream W) r = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  simp only [OracleEnsemble.random_O, oracleDist_apply, lazyDist_apply]
  exact (QueryTree.uprob_evalLazy (· = true) ((OracleAdversary.boundedBy_iff A q).1 hA r)).symm

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
    cases h : next hist with
    | ret b => rw [buildTree_zero_of_ret h]; exact QueryTree.boundedBy_ret b 0
    | query x => rw [buildTree_zero_of_query h]; exact QueryTree.boundedBy_ret false 0
  | q + 1, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_succ_of_ret h]; exact QueryTree.boundedBy_ret b (q + 1)
    | query x =>
      rw [buildTree_succ_of_query h]
      exact (QueryTree.boundedBy_query_succ x _ q).2
        fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

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
  (OracleAdversary.boundedBy_iff _ q).2 fun r => by
    rw [NUPPT.toOracleAdversary_eq]
    exact buildTree_boundedBy _ q []

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
      uprob (fun z : σ × D.Coins n => (D.toOracleAdversary n n n 0 z.2).eval (X z.1) = true) =
        uprob fun r : D.Coins n => b r = true := by
    intro σ _ _ X
    rw [← uprob_snd (α := σ) (fun r : D.Coins n => b r = true)]
    refine uprob_congr fun z => ?_
    rw [hb z.2, QueryTree.eval_ret]
  rw [prfAdv_eq, key (F n), key (fun R => R), sub_self, abs_zero]

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
`perCall(n) + 1` rounds of `run` (the last returns the answer; a further query after the budget
is spent is cut off with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
joint default, unlike `PolyHandler.answer`, which defaults each component separately).

The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
output on a malformed round output or on a further query after the budget is spent. (A return at
zero remaining budget is accepted: only a query then hits the timeout.) -/
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
is the all-`false` answer and state (`decodeBitMove`'s default), and so is a further query after
the budget is spent (a return at zero remaining budget is accepted). -/
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []

/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
`perCall(n)` and the all-`false` result on a query after it is spent: `H.call n z ω s i x =
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
(`decodeBitMove`'s default), and so is a further query after the budget is spent (a return at
zero remaining budget is accepted). -/
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []

/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
`finCall(n)` and the all-`false` output on a query after it is spent: `H.finish n z ω s a =
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

/-- The left oracles of the union have the queries of `s₁`: `(s₁.add s₂).dom (.inl i) = s₁.dom i`. -/
theorem OracleSpec.add_dom_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
    (s₁.add s₂).dom (.inl i) = s₁.dom i := rfl

/-- The right oracles of the union have the queries of `s₂`: `(s₁.add s₂).dom (.inr j) = s₂.dom j`. -/
theorem OracleSpec.add_dom_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
    (s₁.add s₂).dom (.inr j) = s₂.dom j := rfl

/-- The left oracles of the union have the answers of `s₁`: `(s₁.add s₂).rng (.inl i) = s₁.rng i`. -/
theorem OracleSpec.add_rng_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
    (s₁.add s₂).rng (.inl i) = s₁.rng i := rfl

/-- The right oracles of the union have the answers of `s₂`: `(s₁.add s₂).rng (.inr j) = s₂.rng j`. -/
theorem OracleSpec.add_rng_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
    (s₁.add s₂).rng (.inr j) = s₂.rng j := rfl

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

## ===== TCSlib/Cryptography/Games/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
[VCVio, OracleComp/ProbComp/Basic] -/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- Sampling `Fin (m + 1)` is one query to the `m`-th sampling oracle:
`sampleFin m = .query m () .pure`. -/
theorem sampleFin_eq (m : ℕ) : sampleFin m = .query m () .pure := rfl

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- Sampling `T` is sampling an index below `|T|` and reading it through `Fintype.equivFin`:
`sample T = (fun j => (equivFin T).symm (Fin.cast _ j)) <$> sampleFin (|T| − 1)`. -/
theorem sample_eq (T : Type) [Fintype T] [Nonempty T] :
    sample T = (fun j : Fin (Fintype.card T - 1 + 1) =>
      (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
        sampleFin (Fintype.card T - 1) := rfl

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

end ProbComp

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

/-- An implementation is a function of the oracle, the query and the state:
`QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. -/
theorem queryImpl_def {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :
    QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ) := rfl

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
  | pure a => simp only [OracleComp.pure_bind, simulate_pure]
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  rw [← OracleComp.bind_pure (OracleComp.call i x), OracleComp.call_bind, simulate_query]
  simp only [simulate_pure]
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
    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) := by
  rw [passthrough, ofComp_apply, OracleComp.call_bind]

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
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
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
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
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
  | pure a =>
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure cost' (a, s) q
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query b i x k q).1 hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rw [Nat.add_sub_cancel' hi] at h
    rw [simulate_query]
    exact h

end TCSlib.Cryptography.Games

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

/-- `A` makes at most `q` queries iff the tree of every coin string does:
`A.BoundedBy q ↔ ∀ r, (A r).BoundedBy q`. -/
theorem OracleAdversary.boundedBy_iff {ρ : Type*} {I O : Type} (A : OracleAdversary ρ I O)
    (q : ℕ) : A.BoundedBy q ↔ ∀ r, (A r).BoundedBy q :=
  Iff.rfl

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

omit [Fintype P] [Fintype V] [Nonempty V] [Fintype ρ] in
/-- On the answer stream `a` and coins `r`, `lazyDist A` is the lazy run of `A r` from the empty
list of distinct queries: `lazyDist A a r = (A r).evalLazy a []`. -/
theorem lazyDist_apply (A : OracleAdversary ρ P V) (a : ℕ → V) (r : ρ) :
    lazyDist A a r = (A r).evalLazy a [] :=
  rfl

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
