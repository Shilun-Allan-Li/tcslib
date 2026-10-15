# Chapter 7 fill-gate audit findings

**Result: 0 blockers, 0 majors, 2 minors, 2 notes.** I found no block-index, majority-threshold, nested-length, or missing-hypothesis defect in the added formal statements. The two minors concern inaccurate descriptions of the delivered implementation/API. This is a bounded statement audit, not a blanket approval of the repository, the earlier statement gate, or the execution attestations.

Audited artifact: the supplied `ch7-fill-bundle.md`, SHA-256 `00be8b1d71cf1e9512438c2b5ddfdf0987753c09e70ef4249b0636f61593e4b2`. All nine bundled Lean files match [a-gupte/tcslib at `0c22ae33a2321ea027261efa3608ad952b3cd9a5`](https://github.com/a-gupte/tcslib/tree/0c22ae33a2321ea027261efa3608ad952b3cd9a5), after removing the bundle's fences. Historical comparisons used baseline `76fe2f46333c9b1006c6dd8c8c27d55c76586024`.

I consulted Arora–Barak's January 2007 Chapter 7 draft, specifically Theorems 7.8, 7.10, 7.17, 7.18 and Corollary 7.11. The corresponding [author-hosted chapter](https://theory.cs.princeton.edu/complexity/bppchap.pdf) identifies the source. Theorem 7.8's proof is left as an exercise; the present OR machinery supplies an implicit closure used by the formalization. Majority repetition and the XOR-shift membership test have the intended chapter-level meanings. Probability estimates and previously accepted deviations were not reopened.

**Method.** I extracted declarations with comments removed and theorem proof bodies omitted; recorded independent restatements; then compared the docstrings. The audit pack's descriptions had necessarily been read first. I examined definitions and contracts, including private state definitions needed to understand the public functions, without reviewing tactic proofs. Questions 1–2 were checked before 3–6. Executable checks below are independent Python models of the definitions, not Lean execution or substitutes for proof.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `ClassNP/PolyTimeBlockLoop.lean` · module `Main results`, `polyTimeComputable_xorD` | The module summary still attributes XOR to the abandoned one-pass counter-program construction. | It says “polynomial-time (a one-pass counter program).” The delivered state definitions `xorPairStep`/`xorPairEmit`, the theorem's own explanation, and the pack describe the emit-iteration construction. | Replace that parenthetical with “via the emit-iteration loop.” No formal statement change. |
| 2 | minor | `TuringMachine/Build/EmitIterEmbed.lean` · module `Main results`; `audits/ch7-fill-pack.md` · scope row | Two advertised reusable embedding lemmas are actually private in another module. | `control_step` and `control_step'` are declared `private theorem` in `EmitIterBody.lean`; neither is a public declaration of `EmitIterEmbed.lean`. They cannot be consumed under the advertised public names `Turing.control_step` and `Turing.control_step'`. | Correct the module summary and pack inventory to describe private body helpers. If a public API is intended, explicitly export/move them and recheck the affected modules. |
| 3 | note | `ClassNP/PClosure.lean` · all three `mem_P_of_block*` | These languages are total extensions through default decoding, not languages that reject malformed encodings. This is compatible with `polyTimeModel`. | With `a'=1`, `k'=0`, and `V=univ`, the malformed word `[]` belongs to every headline language. Queries are re-encoded valid pairs; the efficiency witness constrains precisely those queries. | Keep the statements. State explicitly that exact verifier agreement is on encoded inputs, with default-decoding extensions elsewhere. |
| 4 | note | `EmitIterBody.lean` · `FinTM.exists_emitIterTM`; `PolyTimeBlockLoop.lean` · `polyTimeComputable_emitIter` | The all-iterations orbit bound is sufficient and usable here, but excludes some natural polynomially scheduled computations. | For `g s = s ++ [false]`, `\|g^[i] w\|=\|w\|+i`; no fixed `b,l` bounds every `i`. Nevertheless polynomially many such steps, even emitting each state, take polynomial time. | Preserve the explicit hypothesis. A future generalization can bound only the scheduled orbit, including the final state update; it is unnecessary for these customers. |

**Question 1 — block fidelity.**

Use the pack's `q = a·(n+1)^k` and `K = a'·(n+1)^k'`. On `z = pairEncode x r`, `n=|x|` and the definition reduces exactly to

\[
\operatorname{blockAt}\ a\ k\ (\operatorname{pairEncode}\ x\ r)\ i
= (r.\operatorname{drop}(i q)).\operatorname{take}(q).
\]

Thus `i=0` starts at the first symbol, adjacent full blocks meet at the correct boundary, and `range K` contains exactly indices `0,…,K−1`. Short final blocks remain short; blocks beyond the end are empty; surplus input after the scheduled blocks is ignored. No hidden padding or length rejection occurs. This is the identical slicing in `anyVerifier` and `majorityVerifier`.

For `w = pairEncode (pairEncode x u) v`, `pairFstD w = pairEncode x u`, so `blockAt a k (pairFstD w) i` slices `u` with `q` scheduled at `|x|`. The repetition count also uses `pairFstD (pairFstD w) = x`. It does not use the length of the encoded inner pair, of `u`, or of `v`.

The generic loop emits at indices `0,…,R`, where `R=a'·(|w|+1)^k'`. A block customer first constructs an initialized state containing a unary countdown of length `K`. For its orbit, the chunk is empty for `i<K`, the singleton aggregate is emitted at `i=K`, and the state becomes `blockDone` at `i=K+1`, after which chunks are empty. The generic bound is evaluated at the initialized state's length, which dominates `n`, so it covers the emission at `K` and can include harmless later rounds. There are exactly `K` decider queries. The `+1` permits the final emission; it does not add a vote.

**Definition restatements, recorded before reading the corresponding Lean docstrings:**

| Definition | Independent meaning |
|---|---|
| `polyLen a k` | The explicit schedule `n ↦ a·(n+1)^k`; no arbitrary bounded function is accepted in its place. |
| `boolVerifier M` | Return `some (M x r)` on every input; never return `none`. |
| `anyVerifier M p k` | OR `M` on the `k(\|x\|)` consecutive, possibly short or empty, length-`p(\|x\|)` slices of `r`. |
| `majorityVerifier M p k` | Count true answers on the same slices and test `k(\|x\|) < 2·votes`; a tie rejects. |
| `shiftOrVerifier M p k` | Slice `u` using schedules at `\|x\|`; zip-XOR each slice with `v`, truncating to their minimum length; OR the `M x` answers. This definition returns `Bool`. |
| `polyTimeModel` | Two existential languages in `P` agree with an option-valued verifier's true/false answers on every genuine pair encoding. The two-witness version uses one language and left-nested encoding. Malformed-word membership is unconstrained. |
| `ClosedUnderMajority`, `ClosedUnderAny` | For every efficient Boolean verifier and all four fixed natural schedule parameters, the specified aggregated Boolean verifier is efficient. |
| `ClosedUnderShiftOr` | Under the same premise and schedule quantification, the three-input shifted-OR Boolean predicate has an efficient nested-pair language. |
| `blockAt` | Default-decode, drop `i·q` from the second component, then take `q`, with `q` determined by the first component's length. |
| `sliceTakeAt`, `sliceDropAt` | Re-encode the decoded first component with, respectively, the `q`-prefix or the remainder after dropping `q` from the decoded second component. |
| `blockDone` | `pairEncode [] []`, the two-bit separator word, rather than the empty word. |
| `isNilB` | The Boolean test for the empty list. |
| `xorD` | `zipWith xor` of the two default-decoded components. Both projections of an invalid pair are empty, so invalid pairs produce `[]`. |
| Private `xorPairStep` | Drop one symbol from each decoded component and re-encode them. |
| Private `xorPairEmit` | Emit the XOR of the two heads if both components are nonempty; otherwise emit nothing. |
| Private `anyInit` | Initialize a one-bit false accumulator, a unary countdown of length `K`, and the normalized pair of input and remaining randomness. |
| Private `anyStep` | An empty accumulator or countdown goes to `blockDone`. Otherwise test the next block, replace the accumulator by `[true]` on success, retain it on failure, remove one countdown token, and drop one block. |
| Private `anyEmit` | Emit the nonempty accumulator only when the countdown is empty. On initialized orbits it is one bit; on arbitrary states it can be a longer word. |
| Private `xorInit` | Initialize `[false]`, a countdown scheduled at the inner `\|x\|`, and payload `pairEncode v (pairEncode x u)`. |
| Private `xorStep` | Use the OR guards and update, but query `pairEncode x (zipWith xor v block)`; keep `v` and `x`, advance `u`, and decrement the countdown. |
| Private `majInit` | Initialize marker `[true]`, a unary countdown, empty yes/no unary counters, and the normalized input/randomness pair. |
| Private `majStep` | Use the same termination guards; increment exactly the yes or no counter according to the next query; decrement the countdown and advance one block. |
| Private `majEmit` | At countdown exhaustion with a live marker, emit the negation of `yes.length ≤ no.length`, hence strict comparison `yes > no`. Otherwise emit nothing. |

The imported pairing conventions were also checked: `pairEncode x r` duplicates each bit of `x`, appends `[false,true]`, then appends `r`. `pairDecode` consumes equal bit-pairs until that separator and fails on any other pattern. `pairFstD` and `pairSndD` map decoding failure to `[]`. In particular, an empty first projection alone does not imply malformed input: genuine encodings with empty first component also have that projection.

**Question 2 — headline-statement fidelity.**

The three added theorems make these claims for every fixed `a,k,a',k'` and every `V ∈ P`:

| Headline | Independent statement restatement |
|---|---|
| `mem_P_of_blockAny` | The language of all words `z` for which some `i<K` satisfies `pairEncode (pairFstD z) (blockAt a k z i) ∈ V` belongs to `P`. |
| `mem_P_of_blockMajority` | The language of all words for which `K` is strictly less than twice the number of accepting block queries belongs to `P`; that count uses `MultiTapeTM.indicator V`. |
| `mem_P_of_blockXorAny` | Decode an outer pair and its first component; use the inner first component as `x`, inner second as `u`, and outer second as `v`. The language accepting some query `pairEncode x (zipWith xor v (blockAt a k (pairFstD w) i))`, with both schedules at `\|x\|`, belongs to `P`. |

Let `V` be the true-answer language in the efficiency witness for `boolVerifier M`. For every `x,r`, the witness gives `pairEncode x r ∈ V ↔ M x r = true`. Every individual block query is a genuine encoding, so its indicator equals the corresponding Boolean answer of `M`. Replacing indicators with those answers makes the first headline exactly `anyVerifier` and the second exactly `majorityVerifier` on `pairEncode x r`. Repeating the calculation with the three decoded components makes the third headline exactly `shiftOrVerifier` on `pairEncode (pairEncode x u) v`.

This needs no hypothesis on the lengths of `r,u,v`. In the book's equal-length shift setting, truncation disappears. On other inputs it agrees with the already audited verifier definition.

The majority state has yes-count equal to the number of successful queries and no-count equal to `K−yes`; both count exactly the scheduled queries, including queries on empty blocks. Consequently

\[
\neg(\mathrm{yes}\le K-\mathrm{yes})
\quad\Longleftrightarrow\quad K<2\,\mathrm{yes}.
\]

The required false-answer witness is the complement of the **final aggregate language**, because these Boolean verifiers never abort. Applying strict majority to `Vᶜ` would mishandle even ties: at one yes and one no, both strict majorities reject. The shifted-OR closure itself only needs a true-answer language through `EffTwoWitness`; a Boolean option-wrapping would permit the same complementation argument.

For malformed words the headline predicates evaluate the verifier on the default-decoded components. They therefore need not reject malformed encodings. This causes no dependence on the arbitrary values of the original witness language off valid encodings: every query to that language is re-encoded first. For a valid outer pair with an invalid inner pair, only the inner components become empty; the outer second component is retained as the XOR mask.

**Adversarial instantiations.** Here bit strings are written as lists of `0`/`1`, and each stated test is a total, polynomial-time predicate.

| Case | Predicted and checked behavior | Error exposed if present |
|---|---|---|
| `a'=0`, including `k'=0`, with `V=univ` | `K=0`. All three aggregate outputs are `[false]`; the initialized state emits once at index `0`, with zero decider queries. | An accidental first query or an empty-output result. |
| `a=0`, `K=3`; accept exactly the empty queried word | All three queries use an empty block; OR and majority accept. The XOR queries also remain empty for every mask. | Treating zero-size blocks as zero repetitions, or failing to advance the countdown. |
| `k=k'=0` | `q=a`, `K=a'`, independent of input length. No `0^0` ambiguity arises because the base is `n+1`. | Exponent-zero schedule errors. |
| `q=1,K=1,r=[1,0]`; accept `[1]` | OR and majority accept using the first bit. | One-based block indexing. |
| `q=1,K=2,r=[0,0,1]`; accept `[1]` | Both aggregates reject; the trailing `1` is outside the schedule. | An extra vote caused by the loop's `+1`. |
| `q=1,K=2,r=[1,0]`; accept `[1]` | OR accepts; majority rejects. At `K=3`, one true vote rejects and two accept. | Non-strict comparison or an off-by-one majority threshold. |
| `q=3,K=3,r=[0,1,1,1,0]`; accept only `[]` | Blocks are `[0,1,1]`, `[1,0]`, `[]`. OR accepts and majority rejects. | Padding, dropping a short block, or terminating queries when randomness ends. |
| `x=[0],u=[0,1,1,0],v=[1,1]`, `a=k=a'=k'=1`; accept `[0,1]` | `q=K=2`; shifted blocks are `[1,0]` and `[0,1]`, so shifted OR accepts. The encoded inner pair has length `8`, which would give a wrong schedule value `9`. The actual loop makes two queries and emits at index `2`. | Using the outer first-component length instead of inner `\|x\|`. |
| Same `x,u`, but `v=[1]`, `q=K=2`; accept `[0]` | Shifted words are `[1]` and `[0]`; shifted OR accepts. | Nontruncating XOR or a hidden equal-length requirement. |
| Malformed `z=[]` or `[1,0]`; `V=univ`, `a'=2,k'=1` | Both decoded components are empty; `K=2`. All headline predicates accept after two queries on canonical encodings of empty components. | An incorrect assumption that malformed inputs reject, or that `V` is queried on the original malformed word. |
| `w=pairEncode [1,0] [1,1]`, invalid inner pair; accept an empty randomness argument | Inner `x,u` become empty, the mask stays `[1,1]`, and each XOR query is empty. With `K=2`, shifted OR accepts. | Incorrect normalization of nested pairs. |
| `V=∅` and `V=univ` | For `∅`, every aggregate rejects. For `univ`, every aggregate accepts exactly when `K>0`, equivalently `a'>0`. | Vacuity or accidental positive-round assumptions. |

The executable model checked 6,696 raw-word/parameter/predicate combinations, 1,350 valid-pair cases, and 1,890 nested-pair cases: **29,808 aggregate checks**, all matching. Each comparison also checked that the output was a singleton, the sole emission occurred at `K`, and exactly `K` decider queries occurred. The raw words covered every bit string of length at most four; schedules included coefficients `0,1,2` and exponents `0,1`; the six predicates included always false, always true, emptiness, first bit, parity, and length equality. These finite checks support the explicit definitional arguments; they do not establish the general theorem.

**Question 3 — loop statement and budget.**

Blind restatement of `FinTM.exists_emitIterTM`: given fixed machines `G,E` computing the total word functions `g,e` within budgets `CG·(n+1)^cG` and `CE·(n+1)^cE`, and fixed naturals `a',k',b,l` satisfying the displayed bound for **every initial word and every iterate**, there exist one finite machine and fixed naturals `C,c` computing

\[
\bigl(\operatorname{range}(a'(|w|+1)^{k'}+1)\bigr)
.\operatorname{flatMap}\bigl(i\mapsto e(g^{[i]}w)\bigr)
\]

within `C·(n+1)^c`. `polyTimeComputable_emitIter` is its FP-level counterpart. No one-bit restriction is imposed on `e`, and no dependence of `C,c` on the individual input is permitted by the quantifier order.

The budget is substantively polynomial. For an orbit state of length at most `b·(n+1)^l`, the two given monomial budgets are polynomials in the original `n`. The one-symbol-per-step output model bounds the lengths of `g s` and `e s` by those budgets. The imported clean-call contracts bound a call by a constant times its original time, input length, output length, and one extra unit. Startup takes `3n+4` steps. Polynomial fuel computation and the imported loop bound `c·(T(n)+1)·(R(n)+2)` then preserve a polynomial bound. These are bounds on fixed contracts; testing whether a state belongs to an orbit is not a runtime operation.

The customers' stated envelopes genuinely cover arbitrary initial state words, not only well-formed initialized states: `2·(|w|+1)` for `anyStep` and `xorPairStep`, and `17·(|w|+1)` for `xorStep` and `majStep`. Countdown exhaustion and absorbing states bound the growing unary vote counters. Thus the hypothesis is nonvacuous for the actual clients.

Additional adversarial cases:

- With `g` the identity, `e s=[true,false]`, and `a'=2,k'=0`, the result consists of three two-bit chunks, `[true,false,true,false,true,false]`. With `a'=0`, the generic result is `e w`, whereas a zero-vote aggregate emits `[false]`. Both follow the specified inclusion of index zero.
- `cG=cE=0` is meaningful: take `g s=[]` and `e s=[true,false]`, with sufficiently large constant budgets and `b=l=1`. The initial state is covered and later states are empty. The constructed host can still have positive-degree overhead; the conclusion does not promise constant total time.
- Since the envelope includes `i=0`, choices `b=0` or `l=0` cannot satisfy it over all input lengths. These are unsatisfiable premises for those parameter choices, not a defect in the usable cases.
- The append-one-symbol function in finding 4 is a natural customer excluded by the all-iterations requirement, even though its scheduled computation is polynomial. The theorem is a sufficient closure principle with an explicit restriction.

**Question 4 — embedding and dispatch.**

| Definition or statement | Independent restatement and assessment |
|---|---|
| `SafeRun` | `runFrom c t=c'`, excluding the avoided state at every `j<t`. The start is included when `t>0`; the endpoint is excluded. There is no liveness requirement. |
| `SafeRun.zero`, `.cons`, `.trans` | Respectively: the zero-step identity; prepending a non-avoided step; concatenating two safe runs with additive durations. These use the same half-open interval. |
| `padAction` | Preserve input movement and optional output. Copy the first `m` tape actions, put no-write/zero-movement actions on all remaining tapes, and apply the supplied function to the optional next state. |
| `embedCfg` | Map the optional state; preserve input head/output; copy the first `m` work tapes and heads; initialize extra tapes blank with heads at zero. It does not carry arbitrary pre-existing padding-tape contents into its result. |
| `embedCfg_ofWords` | A word-initialized configuration embeds as the same word assignment padded with empty words. |
| `padAction_apply` | Applying the padded action to an embedded configuration gives the embedded module action result, even if the current host state was overwritten. |
| `embedCfg_workTapeSymbols` | Reading the initial tape indices through `Fin.castLE` recovers exactly the module's work symbols; changing the current state does not affect this. |
| `embedCfg_output` | Replacing the output field commutes with embedding. |
| `runFrom_one` | One step of `runFrom` equals `step`. |
| `runFrom_of_halted` | A `none` state freezes the whole configuration for every subsequent duration. |
| `state_isSome_of_runFrom` | If the endpoint state is live, every state at `j≤t` is live. |
| `embed_step` | Given a live module state `q` and a host state `b` whose transition is precisely the padded module transition on all symbol observations, one host step agrees with the embedded module step. |
| `embed_run` | If transitions match at every module state except `ex`, and the module is live and off `ex` at each `j<t`, then the entire `t`-step result embeds exactly. Arrival at `ex` or halting at the endpoint is allowed. |
| Private `control_step`, `control_step'` | A pure control transition changes only the state; with input movement, it additionally changes only the input head via `moveInputPos`. Their contracts are appropriate, but their advertised visibility is wrong: finding 2. |

`Fin.castLE` preserves the numerical tape index, so distinct module tapes remain distinct. Padding actions leave later tapes untouched. The two clean-call modules deliberately reuse the initial tape bank sequentially; their interface restores a canonical configuration before dispatch. The lemmas do not promise to preserve arbitrary nonblank padding configurations under `embedCfg` itself.

The parameter named `inject` is only a function; it has no `Function.Injective` hypothesis. That is harmless for the stated forward simulation: the exact transition-compatibility premise supplies what it needs. No theorem claims that state labels can be recovered. The actual body uses distinct constructors `callE` and `callG`, which do give disjoint tags.

The exit condition has the right endpoint convention. For a one-step module run reaching `ex`, only time zero must be off-exit; the theorem transports arrival at `ex`. Trying to transport the next host step would violate `hstate`, appropriately, because the host dispatches there instead of following the module transition. Entry-equals-exit is also handled: `anchor` and `gStart` execute the module's first action directly, and the remaining positive-time segment excludes the exit until its endpoint. The private `body_round` contract uses `0<t'<t`, unlike `SafeRun`'s startup interval `t'<t`; an anchor-to-anchor round cannot be a positive-duration `SafeRun` avoiding its starting anchor.

The remaining private definitions were independently restated as follows:

| Definition | Independent meaning |
|---|---|
| `BodyState` and its finite-type instance | Six distinct startup/dispatch states plus separately tagged emitter and installer states; the type is finite when the two machine state types are finite. |
| `emitIterBody` | Use `max Em.k Gm.k` tapes. Copy the input to tape zero, rewind that tape and the native input, enter `anchor`, call the emitter, dispatch its exit to `gStart`, call the installer, then return to `anchor`. Padding uses the initial tape indices. |
| `copyCfg` | In copy state, assign the first `i` input symbols to tape zero when that index exists; its head is at `i`, the native input head at `i+1`, other tapes blank, output empty. |
| `fullCfg` | Assign the full input to tape zero when present, with the specified control state, native input position, and tape-zero head; other tapes and output are empty. |

The positivity premises on the two clean-call tape counts prevent losing the state word through a zero-tape representation. For an empty native input, the startup contract still specifies four steps to reach the canonical anchor configuration; no positive-input-length assumption is hidden.

**Question 5 — output-prefix commutation.**

Blind restatement of `step_output_prefix` and `runFrom_output_prefix`: replacing initial output by `pre ++ c.output` prefixes the resulting output by the same `pre`, while every other resulting configuration field is unchanged. The latter holds for every natural duration. `runFrom_output_extends` separately states that final output is initial output followed by some suffix.

These are the appropriate contracts for an output-blind, append-only machine. They are strong enough for the assembly because the install-call contract ends in `Cfg.ofWords`, whose output is empty. Starting that call with an already-emitted chunk therefore ends with exactly that chunk and the newly installed state word. Prefix commutation alone would not establish absence of additional output; the empty-output endpoint is essential.

The stronger claim that the install call emits nothing at any intermediate time follows from append-only output and its empty-output endpoint: if a nonempty prefix had appeared, later steps could not erase it. No inspection of its transition proof is needed. This also handles a multi-bit previously emitted chunk.

**Remaining public FP/helper statement restatements.** These complete the new public statement inventory beyond the headliners and machine contracts above.

| Statements | Independent meaning |
|---|---|
| `polyTimeComputable_sliceTakeAt`, `polyTimeComputable_sliceDropAt` | Each displayed total slicing/re-encoding function is FP for fixed natural `a,k`. |
| `polyTimeComputable_tail`, `polyTimeComputable_take1` | Dropping or taking one symbol is FP; both return `[]` on empty input. |
| `polyTimeComputable_headD` | Returning the head as a singleton is FP, with `[false]` on empty input. |
| `polyTimeComputable_isNil` | The singleton emptiness bit is FP. |
| `polyTimeComputable_or`, `polyTimeComputable_not` | Pointwise OR of two FP singleton tests, and negation of one, remain FP singleton tests. |
| `pairFstD_nil` | The empty word has empty first default projection. |
| `length_pairSndD_le` | The second default projection has length at most the input length. |
| `eq_pairEncode_of_pairFstD_ne` | A nonempty first default projection certifies that re-encoding both projections recovers the original word. No converse is asserted. |
| `length_pair_components_le` | Twice the first projected length plus the second projected length is at most the original length, also on malformed words. |
| `length_sliceDropAt_le` | Reconstructing after dropping a slice has length at most `max z.length 2`, accounting for canonicalization of a short malformed word. |
| `flatMap_range_eq_single` | If `K<N` and all chunks in `range N` are empty except the prescribed chunk at `K`, their concatenation equals that chunk, of any length. |
| `polyTimeComputable_xorD`, `xorD_pairEncode` | The total truncating XOR function is FP; on genuine pair encodings it is precisely `List.zipWith xor`. |
| `polyTimeComputable_blockAnyTest`, `polyTimeComputable_blockXorAnyTest`, `polyTimeComputable_blockMajorityTest` | From an FP singleton indicator of `V`, obtain exactly one Boolean output encoding the specified aggregate on every input word. |

**Question 6 — additive extension and evidence.**

The baseline's 13 `PClosure` declarations remain an ordered prefix of the current 16. I compared the complete pre-existing declaration text, not just names: after removing comments/whitespace and the new import, it is unchanged. The additions are three ordinary theorems in `namespace Complexity`; there is no new definition, instance, notation, or attribute in that suffix. The new imported implementation modules use the `Complexity` and `Turing` namespaces; the private finite-type instance concerns only the new private body-state type. I found no mechanism that changes existing closure definitions through instance or namespace capture.

For the phase-1 surface, the repository comparison reports eight existing non-`PolyTimeModel` files with changes; each is unchanged after comment/whitespace removal. The other four phase-1 files are absent from the repository diff. `PolyTimeModel` retains the same 20 declaration names, their order and signatures, and exactly the same imports; only the three targeted declaration bodies differ. All nine Lean modules in this attachment match the pinned repository snapshot. These checks corroborate the statement-freeze claim without auditing proofs.

I also read the committed sweep, axiom, and lint logs. They report 19 successful module checks, one intentional admission in `walk_visits_concentration`, and 36 axiom prints of which 35 contain only `propext`, `Classical.choice`, and `Quot.sound`. The exceptional print contains `sorryAx` for that same documented stub. I did not independently run Lean, regenerate oleans, or reproduce those prints. The sweep log identifies `74af662` plus a worktree documentation sweep, so its execution-to-final-snapshot provenance remains a maintainer attestation rather than an independently reproduced build.

The lint log reports `Classes.lean` at **1,329 lines**, rather than the pack's 1,266; the plan's closure row gives the correct 1,329. This discrepancy does not alter the disclosed size finding or the audited semantics. A later split of the counting layer is reasonable provided names, statements, definitions, and required import access are preserved and the affected tree is rechecked. I would not require that refactor to establish fidelity of these fill additions, and this audit does not make a maintainer-reserved decision on it.

No formal-statement repair is proposed. Findings 1–2 should be resolved as documentation/API-inventory corrections. Findings 3–4 delimit the exact guarantees that subsequent work may use.
