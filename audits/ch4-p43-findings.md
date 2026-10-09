# P4.3 statement-gate audit

**Verdict: FAIL — gate remains open.** **1 blocker, 4 majors, 4 minors, 3 notes.** The blocker is a false statement, `exists_adjacency_codec_cnf`. The majors concern the advertised interfaces and proof sketches, not counterexamples to PSPACE-completeness or the space hierarchy theorem.

Input SHA-256, independently recomputed:

`5a52f3982128502b46dfe4914df2ebbcec22d1a792d0df5373b6d348210e9f1e`

The bundle contains **exactly 30 attachments**. Audited baseline asserted by the pack: `200f4693a40f30302efed75a4e23ac31216172b7`, branch `complexity/arora-barak-ch3-4`. Scope: the seven named P4.3 files, **14 definitions and 12 sorried statements**, with the supplied dependencies as context. I read the in-scope declarations with comments stripped before comparing their docstrings. No source files were changed; no sub-agents were used.

The arguments below are mathematical statement audits, **not completed Lean proofs or a fresh elaboration**. “True” means independently supported by the stated construction, not inferred from `sorryAx` or the false codec lemma. The exact commit comparison and build-artifact claims remain unverified; see finding 12.

## Findings

Paths in this table are relative to `TCSlib/Complexity/`, except for the pack and logs. Line numbers refer to the extracted attachments.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **blocker** | `ClassPSPACE/TQBF.lean:122` · `exists_adjacency_codec_cnf` | Windowed **full** configurations admit fixed-length injective codes and exact-step adjacency. | Set `n = s = 0`, keep the state halted, input position fixed, work heads at zero and tapes blank, and vary `output`. There are infinitely many such configurations but only `2^C` length-`C` codes. Section “Counterexample” gives the finite pigeonhole contradiction. Exact-step correctness alone also forces the impossible injectivity on these halted configurations. | Encode a finite, acceptance-preserving quotient, such as `coreSum`, and change **both** equality clauses accordingly; or explicitly restrict to a suitable bounded-output carrier and prove its closure/adequacy. Merely deleting the injectivity conjunct or invoking `coreCode_inj` does not repair the statement. |
| 2 | **major** | `ClassPSPACE/TQBF.lean:122,193` · adjacency package / `TQBF_PSPACEHard` sketch | The existential package supplies the polynomially emittable objects needed by a Karp reduction. | Its prefix is `∀ M, ∃ C, ∀ n s, ∃ code φ`. It specifies neither a uniform constructor nor a computation bound for `code`, the initial/accepting codes, or `φ`. Polynomial description size does not supply a polynomial-time algorithm selecting descriptions. This defect survives repair of finding 1. | Give a joint uniform construction contract, or name a concrete construction plus private polynomial-time construction/serialization obligations used by hardness. Do not claim that the displayed existential interface alone supplies them. |
| 3 | **major** | `ClassPSPACE/TQBF.lean:128,174` · guarded eval equivalence / midpoint recursion | Correctness on encoded configuration pairs suffices when midpoint blocks quantify over all bit strings. | The theorem says nothing about strings outside the codec image. A two-bit example has valid codes `00,11`, only identity edges between valid codes, but additionally permits `00 → 01 → 11`; all valid-pair checks hold while the midpoint formula invents a path. See question 5. | Supply an efficient validity predicate and restrict existential intermediate vertices, or give a total adjacency contract excluding invalid vertices. Include computable initial and accepting predicates and the quotient-to-run bridge. |
| 4 | **major** | `SpaceComplexity/Hierarchy.lean:77` · `space_universal` sketch | Window overflow and a clock implement the stated exact visited-cell test and tagged output. | At `s = 1`, a one-tape machine can visit positions `0,1` and halt without leaving `[-1,1]`, although it used two cells. At `s = 0`, the initial work-cell visit already exceeds the budget. Also, streamed output cannot be retracted when a later overflow/nonhalting verdict must yield exactly `[false]`. | Track the visited interval and reject when its cardinality exceeds `s`, including initial and final configurations. Probe silently, then on success emit `true` and replay while forwarding output. Budget canonization by a finite code-dependent constant, not the unprovided claim `O(length α)`. The theorem statement can remain unchanged. |
| 5 | **major** | `SpaceComplexity/Hierarchy.lean:132` · `space_hierarchy` sketch | The displayed call to `space_universal` proves one uniform `O(g(n))` bound for the diagonal machine. | `C` may depend on the code parsed from the input; `∀ α, ∃ Cα` does not give `∃ C, ∀ inputs`. Calling with budget proportional to `g(n)` gives a code-dependent multiple of `g(n)`. Padding the code can change that constant, contrary to the attached `CodePrefix` discipline. | Cap the diagonal machine's own simulated workspace uniformly, keep one code fixed, and pad the payload. Question 7 gives a repair using capped calls at increasing budgets; it also avoids assuming a tighter cost for a call made with budget `g(n)`. State the space-preserving normal-form and virtual-input obligations. |
| 6 | minor | `ClassPSPACE/TQBF.lean:177,190` · hardness sketch | `ψ₀ = adjacency` starts the induction “path of length at most `2^i`.” | For a live configuration `c` with `step c ≠ c`, zero-step reachability from `c` to itself is true, but adjacency at `(c,c)` is false. Halted self-loops do not fix this at live vertices. | Set the base to valid equality **or** adjacency, or prove exact-`2^i` reachability and separately pad paths at a halted accepting target. This is also a small omission in the book's displayed induction, not a reason to inherit it. |
| 7 | minor | `ClassPSPACE/TQBF.lean:106` · codec construction sketch | The listed state/head/work tracks suffice for an input-independent adjacency formula `φ`. | The listed tracks omit the input symbols and the scanned-input snapshot. A machine changing state according to its scanned input bit has identical listed tracks on one-bit inputs `false` and `true`, but different successors. The formal `code x c` may depend on `x`; the sketch has not used that allowance. | Include a scanned-symbol snapshot and its consistency checks, or carry the read-only input track in the code; alternatively allow an input-dependent formula. Do not assert linear local-check size until these checks and multi-tape coordination are accounted for. Polynomial size remains sufficient. |
| 8 | minor | `ClassPSPACE/TQBF.lean:138` · CNF size measure | The literal-occurrence bound is, by itself, an adequate serialization-size bound. | For `φ = List.replicate r []`, the stated sum is zero and `numVars = 0`, while `CNF.serialize φ` has length `2r + 1`. Empty clauses cost syntax without contributing literals. | Bound clause count too, bound serialization length directly, or prove a normalization retaining at most one empty clause before emission. See question 4 for the exact length equation. |
| 9 | minor | `ClassPSPACE/Games.lean:84` · `determined` sketch | A value meaning “the mover can force a win for their side” obeys the displayed alternating existential/universal recursion with terminal value `W`. | That recurrence keeps **player one's** perspective fixed. A mover-relative value instead changes polarity as the turn changes; at an odd terminal history, `W = true` still means player one won. | Define the value as “player one can force `W = true`,” use OR at even histories and AND at odd histories, and explicitly construct player two's strategy where the value is false. The theorem itself is true. |
| 10 | note | **[P4.2]** `SpaceComplexity/ConfigGraph.lean:119,127,156` · `coreSum`, `CfgStep`, `coreSum_stepWith` | The finite counted vertices and the raw reachability relation have different carriers. | `coreSum` discards unbounded output information down to three cases; `CfgStep` still relates full configurations. The supplied congruence is the right bridge for acceptance. I found no counterexample to these definitions in this review. | No P4.2 repair requested here. File this distinction with that round; finding 1 is a P4.3 misuse of the finite-counting idea, not an inherited false P4.2 definition. |
| 11 | note | `TimeHierarchy/Diagonal.lean:106` and pack question 6 · abstract `code` / “junk codes” | A particular junk string has a specified parser-fallback meaning. | The attached `code` is a choice of an `EffectiveMachineCode`. Its supplied laws ensure total effective decoding and padded encoding round trips, but do not identify a fallback machine for `[]` or another arbitrary string. | Test arbitrary decoded machines, or supply a theorem identifying the selected concrete scheme before asserting a junk string's exact output. This does not harm `space_universal`. |
| 12 | note | Pack provenance and `audits/logs/ch4-p43-*` | The bundle independently establishes the historical diff, fresh elaboration, fresh oleans, and full facade wiring. | The source inventory and text logs check out, but the audited git objects and build artifacts are not in the bundle. The located older checkout does not contain `200f4693`; no historical equality was inferred from it. The logs contain neither per-module exit statuses nor olean freshness evidence. | Retain these as maintainer attestations; attach the seven-file diff and artifact/exit evidence if independent certification is required. No mathematical gate decision here depends on accepting those claims. |

## Counterexample to the codec statement

Fix any `M : FinTM Bool`. Suppose the claimed witnesses exist. Take the resulting constant `C` and specialize to `n = s = 0` and `x = []`.

For each integer `j` with `0 ≤ j ≤ 2^C`, form the configuration

\[
c_j=\{\mathrm{state}:=\mathrm{none},\quad
\mathrm{inputPos}:=0,\quad
\mathrm{workTapes}:=(\lambda i\,z.\,\mathrm{none}),\quad
\mathrm{workTapePos}:=(\lambda i.\,0),\quad
\mathrm{output}:=\mathrm{replicate}(j,\mathrm{false})\}.
\]

All fields are well typed: the empty input has two allowed input-head positions, and there is no restriction on the output list. For every work tape, the head has absolute position zero and every cell outside the zero-radius window is blank. Thus every pair `c_j,c_k` satisfies all four window hypotheses.

The theorem consequently gives

\[
\operatorname{length}(\mathrm{code}\ []\ c_j)=C(0+0+1)=C,
\]
\[
\mathrm{code}\ []\ c_j=\mathrm{code}\ []\ c_k
\Longrightarrow c_j=c_k
\Longrightarrow j=k,
\]

where the last implication follows by taking output lengths. This is an injection from a set of size `2^C + 1` into the binary words of length `C`, a set of size `2^C`. Therefore

\[
2^C+1\le 2^C,
\]

a contradiction. No assumption about the transition table, constructibility, reachability from the initial configuration, or the formula-size bound is needed.

Deleting the explicit injectivity conjunct does not help. Each `c_j` is halted, so `M.tm.step c_j = c_j`, making the formula true on its code paired with itself. If `code [] c_j = code [] c_k`, the formula has the same assignment on `(c_j,c_k)`; the eval equivalence then gives `step c_j = c_k`, hence again `c_j = c_k`.

An acceptance-oriented repair should make the code factor through `coreSum`, identify equal codes with equal summaries and cores, and compare `coreSum (step c)` with `coreSum d`. The supplied `coreSum_stepWith` then supports lifting quotient paths from the actual initial configuration. Forgetting output entirely would lose the acceptance test; retaining its three-valued summary avoids that problem.

## Blind restatements of all 14 definitions

These restatements were obtained from the declaration bodies before reading their docstrings.

| # | Definition | Literal mathematical meaning and comparison |
|---|---|---|
| D1 | `QBF.Quant` | A two-element datatype with constructors `ex` and `all`. Their logical meaning is supplied by the recursion, not by this datatype alone. |
| D2 | `QBF` | An arbitrary pair of a finite quantifier list and a CNF over natural-number variable indices. There is no closure condition tying the two fields together. This is the declared CNF restriction with open matrices permitted. |
| D3 | `truthAux m qs σ i` | Quantify a Boolean at index `i`, overwrite that coordinate of `σ`, increment `i`, and recurse on the remaining list; an empty list asks whether `m.eval σ = true`. The `ex` branch uses existence and the `all` branch uses universal quantification. Coordinates outside the processed interval retain their original values. |
| D4 | `truth Q` | Apply `truthAux` to `Q.matrix`, starting with `Q.quants`, the constant-false assignment, and index zero. A matrix variable beyond the prefix is therefore fixed to false, not implicitly existentially quantified. |
| D5 | `quantBit` | Map `ex` to `true` and `all` to `false`. |
| D6 | `quantOfBit` | Map `true` to `ex` and `false` to `all`. Both compositions with D5 are identities by two cases. |
| D7 | `encode Q` | Encode the quantifier bits as the doubled first component of `pairEncode`, followed by its aligned `false,true` separator and the CNF serialization. No well-formedness hypothesis is required. |
| D8 | `decode x` | On pair success, decode every prefix bit and total-decode the matrix bytes. On pair failure, return the empty prefix and empty CNF. A malformed matrix after a successful pair parse retains the parsed prefix but replaces the matrix by the empty CNF; its truth is still true. |
| D9 | `PSPACEHard L'` | Every binary language in `PSPACE` has a polynomial-time many-one reduction to `L'`. No membership or decidability condition on `L'` is part of hardness alone. |
| D10 | `PSPACEComplete L'` | The conjunction that `L'` belongs to `PSPACE` and satisfies D9. |
| D11 | `TQBF` | The set of all binary strings whose total-decoded QBF satisfies D4. This is a particular totalized string language, not the convention that all malformed encodings are rejected. |
| D12 | `Game.playOut s₁ s₂ n` | Begin with the empty history and append one chosen bit per recursive step. Player one supplies a move when the current history length is even, and player two when it is odd. The resulting history has length exactly `n`. |
| D13 | `Game.FirstWins n W` | There exists one history-dependent strategy for player one such that every player-two strategy produces a length-`n` play with `W = true`. The winning strategy must be fixed before the opposing strategy is chosen. |
| D14 | `Game.SecondWins n W` | There exists one player-two strategy such that every player-one strategy produces `W = false`. This is the correct opposite outcome, not a second existential witness for `W = true`. |

The definitions implement the declared conventions. The differences in D2, D4, D8, D11 and the binary fixed-depth restriction in D12–D14 are explicit restrictions/totalizations, not hidden changes. CNF matrices and unary variable indices preserve polynomial-time completeness when the construction and serialization obligations are actually supplied. Unbound variables fixed to false do not endanger membership or hardness: membership handles them explicitly, and hardness may output closed formulas.

## All 12 sorried statements

| # | Declaration | True-as-stated assessment and argument |
|---|---|---|
| S1 | `QBF.truth_exPrefix_iff_satisfiable` | **True.** Existential witnesses give a total final assignment satisfying the matrix, so the forward implication needs no coverage hypothesis. Conversely choose the satisfying assignment's bit at each index below `n`; `m.numVars ≤ n` ensures agreement on every mentioned variable. |
| S2 | `QBF.decode_encode` | **True.** Apply `pairDecode_pairEncode`, cancel `quantOfBit ∘ quantBit` pointwise, and use `CNF.decode_serialize`. Equality of the two fields gives equality of QBF structures. |
| S3 | `PSPACE_eq_P_of_pspaceComplete_mem_P` | **True.** Hardness and downward closure of `P` under polynomial-time reductions give `PSPACE ⊆ P`. The reverse inclusion follows from the polynomial-space simulation of polynomial-time deciders; the positive polynomial bounds absorb fixed tape-count overhead. |
| S4 | `exists_adjacency_codec_cnf` | **False.** The finite pigeonhole argument above contradicts both its injectivity demand and, independently, its exact-step equivalence on halted configurations. The proof sketch only describes core data, whereas the conclusion distinguishes full output lists. |
| S5 | `TQBF_mem_PSPACE` | **True; even linear space is attainable.** Validate the entire encoding, then traverse assignments depth first with constant-size information per quantified variable and evaluate the serialized CNF by scans. Invalid syntax returns true through the specified fallback; free variables read false. All work fits in `O(input length + 1)` cells without storing a separate restricted formula at every recursion level. |
| S6 | `TQBF_PSPACEHard` | **True as a language-theoretic statement; the advertised proof interface is inadequate.** A valid, uniformly constructible codec of cores plus output summaries yields a polynomial-width finite graph. Apply the guarded midpoint construction from question 5, then prenex conversion, innermost existential Tseitin variables, and polynomial unary serialization. This independent route does not use S4 as written; findings 1–3 must be repaired before the proposed dependency route can be filled. |
| S7 | `TQBF_PSPACEComplete` | **True.** Conjoin S5 and S6 under the definition of `PSPACEComplete`. Its intended proof remains downstream of the unresolved hardness interface. |
| S8 | `Game.determined` | **True.** Backward evaluation of the finite binary game tree determines whether player one can force `W = true`. If so choose a true-valued child at each relevant even node; otherwise choose a false-valued child at each relevant odd node for player two, extending the strategy arbitrarily on unused histories. |
| S9 | `space_universal` | **True, with the corrected construction in question 6.** Effectivity permits finite code-specific canonization overhead, exact interval accounting tests the simulated budget, and a core-count clock decides whether a bounded run halts. A silent first pass followed by replay realizes the output contract without buffering an arbitrarily long output. |
| S10 | `space_hierarchy` | **True, with a uniform cap and fixed-code padding.** Eventual domination plus positivity gives the non-strict inclusion after absorbing finitely many exceptional lengths. The capped diagonal construction in question 7 separates the classes while using a single `O(g)` bound; only the lower floor, not the computability part of `hf`, is needed. |
| S11 | `LOGSPACE_ssubset_PSPACE` | **True.** Apply S10 to `logSpace` and `n + 1`, using the two supplied constructibility contracts and logarithmic domination proved below. A language separating these two bounds also separates `LOGSPACE` from the larger union `PSPACE`. |
| S12 | `SPACE_linear_ne_NP` | **True.** Under the contrary equality, a polynomially padded version of every quadratic-space language lies in linear space and hence in `NP`. Polynomial-reduction closure of `NP` transfers this back to the original language, collapsing quadratic space into linear space and contradicting S10. |

## Answers to the eight questions

**1. Index threading and accumulated updates.** After the first `j` quantifiers starting at index `i`, the assignment agrees with the chosen bits on `[i,i+j)` and with the original assignment outside that interval. Induction proves this: `Function.update` changes exactly `i+j`, and the recursive call advances to `i+j+1`, so it cannot overwrite a previously chosen coordinate. At the leaf, evaluation therefore uses precisely the prescribed quantified coordinates. In particular,

\[
\mathrm{truth}\langle [],m\rangle
\iff m.\mathrm{eval}(\lambda v.\mathrm{false})=\mathrm{true}.
\]

For a closed matrix, varying the initial assignment changes no mentioned variable at the leaf, so it does not change truth.

**2. Coverage of the existential prefix.** `numVars` is one greater than the maximum mentioned index, or zero if none is mentioned. Thus `m.numVars ≤ n` is precisely coverage by the initial segment `[0,n)`; it is sufficient, though not necessary for every particular matrix. Without it, take `m = [[(0,true)]]`, `n = 0`: the matrix is satisfiable but the QBF is false. Forward extraction of a satisfying assignment works without the hypothesis; backward extraction needs the update-agreement argument. At `n = 0`, coverage forces evaluation to be assignment-independent; `[]` is true and `[[]]` is false. Extra existential quantifiers beyond `numVars` change nothing because Boolean quantification is over a nonempty type and those variables do not occur.

**3. Pair alignment and round trip.** The parser reads pairs from the beginning: equal pairs encode prefix bits; the aligned `false,true` pair ends the prefix. An unaligned occurrence of these bits is not a separator. Both quantifier conversion functions are inverse, so the round trip follows exactly as in S2. A separate injectivity hypothesis is unnecessary; the round trip already proves

\[
\mathrm{encode}(Q)=\mathrm{encode}(R)
\Longrightarrow
\mathrm{decode}(\mathrm{encode}(Q))=
\mathrm{decode}(\mathrm{encode}(R))
\Longrightarrow Q=R.
\]

The semantic correctness consumer only needs this round trip; a polynomial-time consumer additionally needs construction and output-length bounds, which the round trip does not assert. Here “malformed” concerns the serialization grammar: a syntactically valid encoding with free matrix variables instead follows the declared false-assignment convention.

**4. Full adjacency-package reading.** For a fixed machine, one positive `C` must work for **all** natural `n,s`. Only then are a total dependent function `code` and a single CNF `φ` selected. The code length is `C(s+n+1)` even on inputs whose length differs from `n` and on nonwindowed configurations; there is no injectivity or adjacency requirement on those extra cases. For inputs of length `n`, both heads and all nonblank work cells of **each** configuration must lie in the window. Under those four assumptions the package demands injectivity into **full configuration equality**, plus the exact deterministic-step test. Neither reachability nor a bound on output is assumed.

The formula is selected before `x` and therefore is the same for every length-`n` input. This is possible with an appropriate input-carrying code, but is not realized by the fields listed in the sketch (finding 7). A corrected code can use padding to meet the exact length and a constant dummy word outside its guarded domain.

On valid concatenated codes, `φ.numVars ≤ 2C(s+n+1)` puts every mentioned variable inside the concatenation; the `getD ... false` default is never consulted for such variables. This is a sound indexing convention. It does not certify that an arbitrary block quantified later is a valid code.

The literal measure is exactly an occurrence count. The attached serialization obeys

\[
\operatorname{length}(\mathrm{CNF.serialize}\,\varphi)
=1+2\varphi.\mathrm{length}
 +\sum_{\text{clause in }\varphi}\ \sum_{(v,b)\text{ in clause}}(v+3).
\]

Consequently, bounding both clause count and literal count, together with `numVars`, bounds the serialized length polynomially. The displayed literal bound alone misses arbitrarily many empty clauses.

At a halted configuration `c`, the required equation really is `d = c`, because `step c = c`. Adding these self-loops preserves acceptance reachability and is a harmless total-step convention. It does not make every live configuration reflexive, nor repair unbounded output.

**5. Membership, midpoint recursion, fresh variables, and hardness.** For membership, the raw input supplies all prefix bits and matrix bytes. The prefix length and every decoded variable index are at most the input length. Validate the complete grammar before committing to a false matrix result: trailing garbage makes the total decoder select the true fallback, even if a scanned prefix looked unsatisfiable. A depth-first traversal stores one of a constant number of phases/values per quantified variable, one current result bit, and cursors; matrix evaluation rereads the input and assignment bank. No stack of copied formulas or logarithmic-size return addresses per variable is needed. The total is `O(n+1)` visited cells, including initialization and parser failure paths.

For hardness, let `ℓ` be the polynomial code width of a **repaired** finite graph. Use an efficiently generated predicate `Valid` for valid vertices, `Next` for adjacency, and `Accept` for halted vertices with accepting output summary. Take

\[
\psi_0(a,b):=
\mathrm{Valid}(a)\land\mathrm{Valid}(b)
\land(a=b\lor\mathrm{Next}(a,b)),
\]
\[
\psi_{i+1}(a,b):=
\exists z\;\Bigl(\mathrm{Valid}(z)\land
\forall u\,v\;\bigl(
((u=a\land v=z)\lor(u=z\land v=b))
\Rightarrow\psi_i(u,v)\bigr)\Bigr),
\]

where every block has `ℓ` Boolean coordinates. For each fixed `z`, specializing the universal pair to `(a,z)` and `(z,b)` gives the two desired subpaths. Conversely, those two subpaths satisfy the implication for every pair, since its antecedent selects exactly those two pairs. The base includes length-zero paths, and splitting/concatenating paths establishes by induction

\[
\psi_i(a,b)\iff
\text{a path of length at most }2^i\text{ joins the valid vertices }a,b.
\]

There are at most `2^ℓ` codes; a shortest reachable path suffices at depth `ℓ`. Quantify an accepting target and constrain the starting code to the actual initial vertex. The quotient congruence lifts a path back to a genuine run and preserves the accepting summary. A unique erased accepting configuration is optional, not needed for this construction.

Finding 3 is independent of finding 1: on a hypothetical repaired finite carrier with image `{00,11}`, let the encoded relation be true on both diagonal valid pairs and whenever at least one endpoint is invalid, but false on `(00,11)` and `(11,00)`. It satisfies the required valid-pair identity-graph semantics. Nevertheless `01` is an existential midpoint giving a two-step path between the distinct valid vertices. A CNF for this four-bit relation exists by the supplied finite Boolean-function lemma.

Allocate disjoint `ℓ`-bit blocks for the midpoint and two universal endpoints at each level. Their quantifier order must follow the recursion, with every newly referenced index bound exactly once in the final initial-segment prefix. The recursion has only one copy of its predecessor, so its added scaffolding has `O(ℓ)` size per level, or `O(ℓ²)` altogether, plus the polynomial-size base/validity predicates. Use constant-arity gate constraints for CNF conversion; applying a truth-table CNF construction to an entire `ℓ`-bit equality or level would instead be exponential.

One safe auxiliary-variable discipline is to prenex the freshened recursion first, then existentially quantify all Tseitin gate values **after** its original prefix. For each complete original assignment, existence of consistent gate values is equivalent to truth of its propositional matrix; quantifying the original assignments preserves that equivalence. Gate values must not be existentially fixed before universal variables on which they depend. All variable indices and the clause/literal counts stay polynomial, so the preceding unary-serialization equation remains polynomial. A **uniform emitter** must still be proved, rather than obtained from S4's unannotated existence statement.

The definition of hardness is exactly polynomial-time many-one hardness; no claim of logspace-reduction completeness is delivered in this phase.

**6. Universal machine: literal clauses and a sound construction.** One machine `SU` is chosen first. For each fixed code `α` there is one positive constant `C`, independent of **both** `s` and `x`. If the decoded deterministic machine has a halting computation within `s` visited cells, the first clause requires the tagged output for every qualifying output/time witness. Determinism makes those output witnesses equal; extra post-halting time does not change output or space. In fact, the first existential antecedent is redundant, because each instance of its inner premises already supplies that antecedent. If no qualifying computation exists, the second clause demands a halting output exactly `[false]`. On well-formed outer triple encodings, the clauses are exhaustive and consistent.

A construction meeting them is:

1. Canonize the fixed code and prepare virtual access to `x`. The effective-scheme contract gives a finite canonizer time and space for this `α`; absorb it into `Cα`. No linear bound in code length is supplied by `EffectiveMachineCode`.
2. Probe the run with output suppressed. The coded machine has one work tape. Maintain the minimum and maximum visited positions, initially both zero, and reject if `max − min + 1 > s`. Unit head moves make this interval exactly the visited set; check a newly reached position even when that step halts.
3. Bound the silent probe by the number of possible cores in the radius-`s` window. For this fixed machine that count is at most
   \[
   (\#M.\mathrm{State}+1)(n+2)3^{2s+1}(2s+1).
   \]
   Its binary counter has `Oα(s + logSpace n + 1)` bits. A repeated live core in a deterministic run makes future control periodic, so no first halt can occur after an undetected repeat; output contents do not affect this argument.
4. On failure output `[false]`. On successful halting, reset the simulated banks, emit `true`, and replay the same run while forwarding its output. Reuse fixed workspace intervals between the two passes; do not buffer the entire output.

The input adapter, budget arithmetic, table/state storage, visited-interval counters, and clock all fit the claimed code-dependent bound. These machine implementations and their space ledgers remain fill obligations.

The logarithmic addend is justified by the `n+2` input-head factor in this clock. This establishes its need for the **proposed clock construction**, not an unconditional lower bound against every possible universal simulation. When `s ≥ logSpace n`, positivity gives

\[
s+\mathrm{logSpace}(n)+1\le 3s,
\]

so it is harmless under the standing above-log convention. Unlike the success-only exercise, the statement also specifies tagged outputs and failure totality; these are valid strengthenings that require the probe/replay work.

For `s = 0`, every coded machine has one work tape and has already visited its origin, so the failure clause applies on every input. For a code of a silent immediate-halting machine, the result at `s ≥ 1` is `[true]`; for a stationary infinite loop it is `[false]`. These examples do not require attributing either machine to a particular “junk” string: the supplied abstract scheme makes no such attribution.

**7. Little-oh, a repaired diagonal argument, and logarithmic domination.** Because `g(n) ≥ 1`, the stated arithmetic hypothesis is equivalent to `f(n)/g(n) → 0`. In one direction, for any positive real `ε`, choose a positive integer `A` with `1/A < ε`; eventually `A f(n) ≤ g(n)`, hence `f(n)/g(n) ≤ 1/A < ε`. In the other direction, for each integer `A > 0` use `ε = 1/A`; `A = 0` is automatic. No monotonicity is needed. When `f = g`, taking `A = 2` contradicts the positive floor, so the theorem is not vacuous on equal bounds.

For the ordinary inclusion, use `A = 1` eventually and absorb the finitely many earlier values of `f` into a multiplicative constant, since `g ≥ 1` everywhere.

Here is one repair of the strictness proof that uses S9's actual interface:

1. On an input of length `n`, compute `g(n)` using its fixed constructibility witness. Parse a fixed-code/payload pair; malformed pairs get a fixed answer.
2. On a valid pair with code `α`, try budgets `s = 0,1,…,g(n)`, reusing the same banks. Run `SU` on the virtual input `pairEncode (Nat.bits s) (pairEncode α originalInput)`, but abort an attempt before a simulated work head of this **fixed `SU`** leaves `[-g(n),g(n)]`.
3. Suppress its output and retain only the finite summary needed to distinguish failure, success with original output `[true]`, and other successful outputs. On the first success, return the opposite of acceptance; if every attempt fails or is capped, return a fixed bit. Each uncapped attempt halts by S9, and there are finitely many attempts.
4. There is now a uniform space bound: `SU` has a fixed number of work tapes, each confined to a fixed window. Budget/input-address counters and bank resets use `O(g(n))` additional cells; virtual input avoids storing the length-`n` original input. This constant is independent of `α`. Canonization inside a call is capped too.
5. Suppose the resulting language had a decider in `SPACE f`. Put that decider into a **space-preserving** one-work-tape code form, with fixed code `α` and bound `c₀ f(n)`. Fix this code and increase only the payload length. Choose the domination constant `A = Cα(c₀+2)`. Since `logSpace n ≤ f(n)` and `1 ≤ f(n)`, eventually
   \[
   C_\alpha\bigl(c_0f(n)+\mathrm{logSpace}(n)+1\bigr)
   \le C_\alpha(c_0+2)f(n)\le g(n).
   \]
6. Therefore all calls up to budget `c₀ f(n)` fit the cap, and a successful call occurs by that budget. Every successful call reports the same deterministic decider output on the original input. The diagonal answer is its opposite, a contradiction.

The bounded interpreter, resetting within fixed banks, virtual-input adapter, and space-preserving normal form need explicit fill contracts. A time-only normal-form theorem is not a space ledger. Also, simply capping **one** call made with budget `g(n)` is insufficient: S9's bound for that call is proportional to `Cα g(n)`, even when the actual simulated machine uses much less. The increasing-budget repair resolves this particular interface problem. Computability of `f` is unused; its bundled logarithmic floor is used in step 5.

For S11, an explicit eventual bound is available. Fix `A ∈ ℕ`, set `K = max(4,2A)`, and take `n ≥ 2^K`. With `k = floor(log₂ n)`, one has `k ≥ K`, and

\[
n\ge 2^k\ge k^2\ge 2Ak\ge A(k+1)=A\,\mathrm{logSpace}(n).
\]

Here `2^k ≥ k²` follows from equality at `k = 4` and induction using `2k² ≥ (k+1)²` for `k ≥ 4`. This proves the required bound, even with `n` instead of `n+1`. Applying the hierarchy theorem and then the degree-one inclusion into `PSPACE` yields strict containment.

**8. Padding and games.** Use the concrete padding function

\[
x\longmapsto \mathrm{pairEncode}\bigl(x,\mathrm{replicate}((\operatorname{length}x)^2,\mathrm{true})\bigr).
\]

For `n = length x`, its output length is `m = n² + 2n + 2`, including at `n = 0`. The padded-language decider verifies this exact syntax/length, rejects other strings, and simulates the original quadratic-space decider on the first component. Its simulation uses `O(n²+1) ⊆ O(m+1)` space. Under `SPACE(n+1) = NP`, the padded language is in `NP`, and the polynomial-time padding reduction puts the original language in `NP = SPACE(n+1)`. This is the correct reduction direction: **unpadded language reduces to padded language**. Downward closure follows by composing the reduction with the bounded-certificate verifier and bounding its certificate polynomial at the polynomially bounded reduction output length.

For the hierarchy contradiction, when `n ≥ max(1,2A)`,

\[
A(n+1)\le 2An\le n^2\le n^2+1.
\]

Use constructibility of `n+1` and `n²+1` (the latter is attributed to the concurrent P4.2 layer; its source file is not attached, so its exact signature/import should be verified at fill time). There is no claim of either inclusion between `NP` and linear space.

For games, length induction gives `length(playOut s₁ s₂ n) = n`, so parity matches the stated convention. For fixed horizon `n`, define the Boolean position value `V(h)` to mean **player one** can force a win. At terminal histories it is `W(h)`; at even nonterminal histories it is the OR of the two child values, and at odd histories it is their AND. If the initial value is true, pick a true child at even nodes; if false, pick a false child at odd nodes. Finite Boolean case analysis suffices, so classical excluded middle and choice are permissible but not intrinsically needed for this restricted theorem. At `n = 0`, the two predicates reduce to `W [] = true` and `W [] = false` respectively. They cannot both hold: play their alleged winning strategies against each other. General game-tree encodings and treatment of draws remain outside the formal statement; assigning a draw to a player changes the winning condition of the original game.

## Adversarial instantiations and verification

| Test | Instance | Result |
|---|---|---|
| A1 | `decode []`, `decode [false]`, `decode [true]` | Pair parsing fails; all three decode to the true fallback and belong to `TQBF`. |
| A2 | `decode [false,true]` | Pair parsing succeeds with empty components; matrix parsing fails; the fallback matrix is true. |
| A3 | Empty-prefix encodings of `[]` and `[[]]` | Their bit strings are respectively `010` and `01100`; the first is in `TQBF`, the second is not. Thus accepting malformed strings does not trivialize the language. |
| A4 | Empty prefix with `m = [[(0,true)]]` | Matrix satisfiable, quantified truth false. Removing S1's coverage hypothesis is unsound. |
| A5 | Prefix of five existential quantifiers with `m = [[(0,true)]]` | True; four unused variables do not matter. Also tested empty matrices and empty clauses at zero prefix length. |
| A6 | Equality CNF on variables 0 and 1 | `∀x ∃y (x=y)` is true; `∃x ∀y (x=y)` is false, checking both quantifier polarity and index order. |
| A7 | `n = 0` game, separately `W [] = true` and false | Exactly the corresponding player's winning predicate holds; the lack of moves is handled correctly. |
| A8 | Codec with `n = s = 0`, all tapes blank, arbitrarily long output | Contradicts fixed-length injectivity; finding 1. The counterexample also works with zero work tapes. |
| A9 | Halted configuration versus distinct halted configuration | Exact-step adjacency must be equality, not arbitrary acceptance equivalence. This also independently forces codec injectivity. |
| A10 | One work tape, `s = 1`, positions `0 → 1 → 1`, then halt | Two visited cells while every head position remains in `[-1,1]`; the proposed window-only detector is insufficient. |
| A11 | One work tape, `s = 0`, immediate halt at the origin | The original run uses one cell and must trigger the universal failure clause. |
| A12 | Emit once, then loop forever at the same work position | The universal result must be exactly `[false]`; forwarding an output prefix during the probe makes this impossible. |
| A13 | Valid identity graph on codes `00,11`, invalid midpoint `01` | On-valid-pair correctness does not prevent a spurious two-step path through an invalid code. |
| A14 | `φ = List.replicate r []` | Literal count zero, serialized length `2r+1`; finding 8. |
| A15 | `f = g` with the constructibility floor | `A = 2` defeats the domination premise; strictness is not asserted for equal bounds. |
| A16 | Increasing padded aliases of one machine code | Effective-code laws give no bound on how the chosen `Cα` changes; padding the payload of one fixed code avoids that dependence. |

An independent Python transcription checked **14,353 encoding round trips**, **1,449 existential-prefix/satisfiability instances**, and **all 278 Boolean winner predicates for binary games of horizons 0 through 3** against strategy enumeration. All passed. The formula family contained all matrices with at most two clauses, each of width at most two, over variables 0 and 1; round-trip prefixes had lengths zero through four. The coverage tests and counterexamples above are mathematical arguments; these finite checks are supplementary and do not constitute Lean kernel certification.

## Source fidelity, attestations, and repair gate

I consulted the 2009 book text, including printed pp. 77, 79–85, 86–87, 92–94, through this [PDF copy of Arora–Barak](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf). The comparisons are to the book itself, not answers on discussion sites. No separate reading of [SM73] or [SHL65] was required by the pack.

Definitions 4.9–4.10 and Theorem 4.13 support the hardness/completeness and QBF targets. Claim 4.4(2) covers arbitrary candidate bit strings; the attached guarded package does not. Theorem 4.8 has the little-oh hypothesis used here. Exercise 4.1 specifies successful simulation, whereas this contract also totalizes failure. Exercise 4.10 excludes draws, and Exercise 3.2 claims inequality without either inclusion. The source comparison does not cure the implementation-specific defects above.

The two declared codec weakenings—width `O(s+n)` and polynomial instead of linear formula size—are acceptable for polynomial-space hardness **after** the carrier, validity, and uniform-construction repairs. The other declared normalization choices are accounted for in the definition/statement reviews. The exact raw-output equality in S4 is an undeclared, fatal mismatch.

The source inventory is:

| Module | Definitions | Sorried statements |
|---|---:|---:|
| `Formulas/QBF` | 4 | 1 |
| `Formulas/QBFEncoding` | 4 | 1 |
| `ClassPSPACE/TQBF` | 3 | 5 |
| `ClassPSPACE/Games` | 3 | 1 |
| `ClassPSPACE` facade | 0 | 0 |
| `SpaceComplexity/Hierarchy` | 0 | 4 |
| `Formulas` facade | 0 | 0 |
| **Total** | **14** | **12** |

The supplied sweep lists all seven modules, starts with the advertised full commit, contains exactly 12 admission warnings at the expected declarations, contains zero `error:` lines, and ends with `P4.3_SWEEP_DONE`. The lint summaries report 0 FAIL / 0 WARN for the 5-file Formulas tree, 2-file ClassPSPACE tree, and 42-file SpaceComplexity tree. The attached Formulas facade now has its QBF imports before the module docstring and includes both Contents entries; the QBF sketch uses the corrected `Complexity.eval_congr_of_lt_numVars` reference. The historical changes from `572304e5`, actual exits, actual olean freshness, and root facade reachability were not independently established. Tactic proofs and the broader P4.2/routine layers were not re-audited.

To close this gate, re-audit the repaired codec carrier and both equality clauses, the actual uniform construction interface, its invalid-code treatment, and the corrected universal/hierarchy sketches. Recommended permanent sanity statements are: quantifier-bit inverse and encoding injectivity; truth of the empty prefix and covered existential prefixes; quotient-code round trip plus rejection/guarding of invalid codes; universal failure at zero budget and correct interval accounting; and game play length, zero-move outcomes, and mutual exclusion. None of the false raw-configuration claims should survive as a frozen fill target.

## Notation glossary

- `c_j`: the halted blank-work configuration with `j` false output bits used in the counterexample.
- `C`, `Cα`: respectively the codec constant and the universal-simulation constant for one fixed code `α`; subscripts here make the existing dependence explicit.
- `ℓ`: bit width of a repaired configuration-quotient encoding.
- `Valid`, `Next`, `Accept`: proposed predicates for valid encoded vertices, one-step adjacency, and accepting vertices.
- `ψ_i(a,b)`: proposed formula for reachability in at most `2^i` steps; `a,b,z,u,v` are `ℓ`-bit vertex blocks in that construction.
- `V(h)`: Boolean value meaning player one can force a win from history `h` at the fixed horizon.
- `A`, `K`, `k`: domination multiplier, the threshold `max(4,2A)`, and `floor(log₂ n)` in the explicit logarithmic calculation.
- `c₀`: a fixed space multiplier for the hypothetical coded decider in the hierarchy argument.
- `Q,R`: the two QBF structures in the injectivity argument. `ε`: a positive real tolerance in the little-oh equivalence. `Oα`: big-oh with constants allowed to depend on the fixed code `α`.
- `n,m`: original and padded input lengths in the padding argument; elsewhere `n,s` retain the pack's input-length and space-budget meanings. `r` counts repeated empty clauses. Other declaration names and symbols are those already used in the bundle.
