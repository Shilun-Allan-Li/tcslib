Independent adversarial audit of the phase-4 skeleton, Arora–Barak Chapter 1.

Audited snapshot: `49d25a273e89bcfa8af9e9e89ec61d1d910c358a`, branch `complexity/arora-barak-ch1`; immediate parent and phase-3 gate: `b61e876d3cb3efc247c5d85311cf513a05ec83ea`. Inputs: the supplied `phase4-bundle.md` and Arora–Barak (2009), §1.4–§1.5.1, PDF pp. 45–49, especially Theorems 1.10–1.11 on PDF pp. 48–49 (printed pp. 22–23). The attached plan, policy, and phase-3 round-2 Argument F were also consulted. This audit was performed by one agent without delegation.

I found one minor numerical error in a new construction sketch, described in finding 1. I found no counterexample to a new theorem statement and no missing machine-construction interface in the two headline assembly arguments. These conclusions are conditional on filling the construction sorries: they do not certify completed Lean proofs or a successful build.

I extracted comment-free declarations and recorded all 18 restatements below before reading the new docstrings and sketches. Existing tactic proofs were outside the review. Here, `M(x) ↓ w` abbreviates `∃ t, M.ComputesInTime x w t`: the machine has halted with completed output `w` by some finite time. It does not describe an intermediate emitted prefix. Write `Mα` for `(c.decode α).toFinTM` when the scheme `c` is fixed.

The blind restatements are as follows. Namespaces are retained where needed to distinguish the two computability predicates.

| File · new declaration | Blind restatement |
|---|---|
| `Finite.lean · FinTM.Computes` | For every input word, the fixed machine halts with exactly the prescribed output word at some input-dependent finite time. No length bound is part of this predicate. |
| `Finite.lean · ComputesInTime.output_unique` | Two completed computations of the same machine on the same input have equal output words, even if their time bounds differ. |
| `Finite.lean · ComputesFunInTime.computes` | Computing a function within a uniform bound depending on input length implies computing that function on every input. |
| `Composition.lean · computesFunInTime_ifEq` | For any fixed Boolean words `w₀,u,v`, some finite Boolean machine returns `u` when its input is exactly `w₀`, and `v` otherwise, within `c*(n+1)` steps for some constant `c` and input length `n`. |
| `Composition.lean · exists_comp_partial` | Every pair of finite Boolean machines has a composite whose completed relation satisfies `M(x) ↓ w ↔ ∃ y, M₁(x) ↓ y ∧ M₂(y) ↓ w`. Neither component is assumed total. |
| `Composition.lean · exists_cond` | If `D` computes the singleton word `[p x]` on every input, there is a machine whose completed relation on `x` is exactly that of `M₁` on `x` when `p x=true`, and of `M₂` on `x` when `p x=false`. Both branches receive the original input; neither branch is assumed total. |
| `Encoding.lean · computesFunInTime_pairEncode_diag` | Some finite Boolean machine computes `α ↦ pairEncode α α` within a constant times `α.length+1`. |
| `Computable.lean · Computes.exists_computesFunInTime` | Over any finite alphabet, a fixed machine computing a total string function admits some natural-valued time bound depending only on input length. No monotonicity or constructibility is required of that bound. |
| `Computable.lean · Complexity.Computable` | A Boolean string function is computable exactly when one finite Boolean machine computes it on every input, with no time bound supplied. |
| `Diagonalization.lean · UC` | For any `MachineCode`, return `false` exactly when the machine decoded from `α` halts on `α` with the singleton output `[true]`; return `true` otherwise. The latter includes divergence and every other completed output. |
| `Diagonalization.lean · UC_eq_false_iff` | `UC c α=false` is equivalent to the existence of a time witnessing that completed singleton output. |
| `Diagonalization.lean · UC_eq_true_iff` | `UC c α=true` is equivalent to the nonexistence of such a time. |
| `Diagonalization.lean · UC_not_computable` | For every `MachineCode`, no finite Boolean machine computes the total function `α ↦ [UC c α]`. The scheme need not be effective. |
| `Halting.lean · HALT` | Return `true` exactly when the input is `pairEncode α x` for some `α,x` and the decoded machine halts on `x` with some output; return `false` on every other input. |
| `Halting.lean · HALT_eq_true_iff` | The true inputs are exactly those paired inputs with a completed decoded computation. |
| `Halting.lean · HALT_pairEncode_eq_true_iff` | On the specified pair `pairEncode α x`, the value is `true` exactly when the machine decoded from that particular `α` halts on that particular `x`. |
| `Halting.lean · UC_computable_of_HALT_computable` | For every effective coding scheme, total singleton-output computation of its HALT predicate implies total singleton-output computation of its UC predicate. |
| `Halting.lean · HALT_not_computable` | No finite Boolean machine computes the total singleton HALT function for any effective scheme. |

Comparison with the source and docstrings: these restatements agree with the new definitions and theorem prose, subject to the numerical sketch error below. The completed singleton convention matches the book's test for output `1`, including its treatment of divergence and non-Boolean outputs. Scheme parametrization, the code-first pairing, and off-image totalization are documented adaptations. The previously accepted waiver of a formal bridge from the book's read-write output model remains a limitation; this round proves statements in the development's append-only model.

Each of the seven new sorries has the following disposition. These are mathematical assessments of the statements and construction outlines, not completed formalizations.

| Sorry'd declaration | Why the literal statement is true, or the needed correction |
|---|---|
| `computesFunInTime_ifEq` | A finite controller compares at most the first `w₀.length+1` input positions against the hardcoded word, treating an early blank or an extra symbol as a mismatch. It then emits the selected fixed output and halts. Its runtime is bounded by a constant depending on the three fixed words, so the stated linear bound follows; all three words may be empty. |
| `exists_comp_partial` | Simulate `M₁` with its emissions redirected into a fresh contiguous buffer, and start `M₂` only after `M₁` actually halts. Simulate `M₂` on that buffer with fresh work tapes and clamped virtual input boundaries; its emissions become the real output. A completed composite run therefore gives both component witnesses, and both component witnesses give a completed composite run. Nontermination in either executed phase prevents composite halting; the boundary initialization needed by this outline is detailed below. |
| `exists_cond` | The hypothesis makes `D` total with exactly one emitted bit in each initialized run, since output starts empty and can only be appended. A finite register retains that bit until `D` halts; the stated rewind procedure returns the input head to position 1 from every possible position. Starting the selected branch with fresh work tapes and empty real output therefore reproduces precisely its completed relation on the original input. Early emission changes none of this because the construction waits for halting. |
| `computesFunInTime_pairEncode_diag` | Two forward passes separated by a rewind compute the required word, including on empty input. The first pass needs two emission steps per input bit, so the sketch's `3n+6` total is incorrect. The explicit schedule below takes `4n+5` steps and therefore establishes the unchanged existential linear-time statement with, for example, constant 6. |
| `Computes.exists_computesFunInTime` | Choose a witnessed halting time for each input. At every fixed length there are finitely many inputs, so take the maximum of their chosen times, using 0 for an empty set. `ComputesInTime.mono` lifts each individual witness to this bound; classical choice also supplies any required decidable equality. This remains valid for an empty symbol type, whose positive-length input types are empty. |
| `UC_not_computable` | The time-bound bridge, `one_work_tape_binary`, and `exists_codeTM` supply a coded total machine for the hypothetical UC decider. Its fixed code round-trips under `decode_encode`, so at that code its completed output is `[UC c α]`. The defining equivalence and output uniqueness imply `UC c α=false ↔ UC c α=true`, a contradiction. Neither an encoder nor a decoder is executed by a machine in this argument. |
| `UC_computable_of_HALT_computable` | Partial composition constructs the diagonal HALT decider and the evaluator-plus-postprocessor branch, while `exists_cond` combines that branch with the constant-true branch. A negative HALT answer implies UC is true. A positive answer supplies an actual decoded halting computation, and the forward universal clause produces its completed output for the postprocessor; output uniqueness identifies the postprocessed bit with UC. All machine-construction steps are supplied by stated declarations, as made explicit next. |

The diagonalization assembles without an effectivity assumption.

Assume `M.Computes (fun α => [UC c α])`. Choose a time bound using `Computes.exists_computesFunInTime`. Apply `one_work_tape_binary` with that bound; its signature has no monotonicity, computability, or constructibility hypothesis on the bound. Then apply `exists_codeTM` to the resulting one-work-tape Boolean machine. These steps supply a `CodeTM` named `N` such that

\[
\forall\alpha,\quad N.\mathrm{toFinTM}(\alpha)\downarrow[\mathrm{UC}\ c\ \alpha].
\]

Set \(\alpha_0=c.\mathrm{encode}(N)\). By `MachineCode.decode_encode`,

\[
c.\mathrm{decode}(\alpha_0)=N.
\]

Consequently,

\[
\begin{aligned}
\mathrm{UC}\ c\ \alpha_0=\mathrm{false}
&\iff N.\mathrm{toFinTM}(\alpha_0)\downarrow[\mathrm{true}]
&&\text{(`UC_eq_false_iff`, round trip)}\\
&\iff \mathrm{UC}\ c\ \alpha_0=\mathrm{true}
&&\text{(total correctness and `output_unique`).}
\end{aligned}
\]

For the second equivalence, the forward direction compares the alleged `[true]` output with the known `[UC c α₀]` output and uses singleton injectivity; the reverse direction substitutes `UC c α₀=true` in the known computation. If the Boolean is false the displayed equivalence makes it true, and if it is true the equivalence makes it false. Thus no pathological or noncomputable-meaning scheme satisfying the round trip makes UC computable. Padding is not needed for this argument, and choosing the fixed code is not a runtime encoding operation.

The HALT reduction also assembles entirely through the stated interfaces.

Fix one witness `U` of `Turing.universal c` and a hypothetical machine `D` computing `[HALT c.toMachineCode s]`. Define, exactly as in the sketch,

\[
p(\alpha)=\mathrm{HALT}\ c.\mathrm{toMachineCode}
  (\mathrm{pairEncode}\ \alpha\ \alpha),\qquad
r(w)=\begin{cases}[\mathrm{false}],&w=[\mathrm{true}],\\
[\mathrm{true}],&w\ne[\mathrm{true}].\end{cases}
\]

Use `computesFunInTime_pairEncode_diag` for a machine `P` computing the self-pair, `computesFunInTime_ifEq [true] [false] [true]` for the postprocessor, and `computesFunInTime_const [true]` for `Mf`. Their timed correctness implies total correctness by `ComputesFunInTime.computes`.

For any total machine computing a function, existence of its prescribed output together with `output_unique` identifies its completed relation with equality to that output. Therefore `exists_comp_partial` applied to `P,D` gives `D'` satisfying

\[
\forall\alpha,\quad D'(\alpha)\downarrow[p(\alpha)].
\]

Two further uses of `exists_comp_partial`, first with `P,U` and then with the postprocessor, give `Mt` satisfying

\[
Mt(\alpha)\downarrow z
\iff
\exists w,\quad U(\mathrm{pairEncode}\ \alpha\ \alpha)\downarrow w
\ \land\ z=r(w).
\]

Apply `exists_cond D' Mt Mf p` to obtain `R`. Its contract is

\[
R(\alpha)\downarrow z
\iff
\begin{cases}
Mt(\alpha)\downarrow z,&p(\alpha)=\mathrm{true},\\
Mf(\alpha)\downarrow z,&p(\alpha)=\mathrm{false}.
\end{cases}
\]

If \(p(\alpha)=\mathrm{false}\), `HALT_pairEncode_eq_true_iff` and Boolean case analysis imply

\[
\neg\exists w,\ M_\alpha(\alpha)\downarrow w
\ \Longrightarrow\
\neg M_\alpha(\alpha)\downarrow[\mathrm{true}]
\ \Longrightarrow\
\mathrm{UC}\ c.\mathrm{toMachineCode}\ \alpha=\mathrm{true}.
\]

The constant branch thus supplies the required completed singleton output.

If \(p(\alpha)=\mathrm{true}\), the same HALT lemma supplies an output `w₀` and a time `t₀` for the decoded run. The forward universal clause supplies the completed computation of `U` with exactly `w₀`, hence `Mt(α) ↓ r(w₀)`. Determinism of the decoded machine gives

\[
\begin{aligned}
w_0=[\mathrm{true}]
&\iff M_\alpha(\alpha)\downarrow[\mathrm{true}]\\
&\iff\mathrm{UC}\ c.\mathrm{toMachineCode}\ \alpha=\mathrm{false},
\end{aligned}
\]

where the first reverse implication uses `output_unique` against the already supplied output `w₀`. Boolean case analysis now gives

\[
r(w_0)=[\mathrm{UC}\ c.\mathrm{toMachineCode}\ \alpha].
\]

Thus both branches provide `R(α) ↓ [UC c.toMachineCode α]` for every input. Only the forward universal clause was used. This argument chooses one evaluator once, requires no common choice across the other universal theorems, never requires totality of `U`, and needs no timed partial-composition theorem. `HALT_not_computable` is then the logical consequence of this reduction and `UC_not_computable`; its existing proof does not remove those underlying sorry dependencies.

The semantic and adversarial checks are as follows.

| Attempt | Result and evidence |
|---|---|
| A non-injective encoder | Impossible: `encode N=encode N'` implies `N=decode(encode N)=decode(encode N')=N'`. The algebraic round trip suffices. |
| A deliberately noncomputable-meaning coding scheme with computable UC | Refuted by the diagonal argument above, which never asks a machine to compute the representation scheme. No effectivity hypothesis is silently imported. |
| Empty code and empty input | `pairEncode [] []=[false,true]`. Hence `HALT c [false,true]=true` exactly when `(c.decode []).toFinTM` halts on `[]`; `UC c []=false` exactly when its completed output is `[true]`. The malformed string `[]` is a different input, on which HALT is false. The reduction uses the genuine pair, so its two cases remain exhaustive. |
| `M₁` diverges after emitting `[true]` | The intermediate emission is not a completed output. The right side of the composition iff is false for every final word, so the composite cannot halt; UC on that self-run is true and the corresponding HALT value is false. |
| `M₁` halts with `y`, but `M₂` diverges on `y` | Output uniqueness excludes replacing `y` by another intermediate word to manufacture a halting witness. Both sides of the composition iff are false for every completed output. |
| Both phases halt, including `M₁=M₂` | Their two witnesses make the right side true, so an always-diverging alleged composite cannot satisfy the contract. Self-composition means two freshly initialized simulations, not reuse of the first run's tapes. |
| Empty intermediate output in partial composition | After an obligatory initial left move, rewind to the first blank and move right. The resulting blank start represents virtual input position 1, which is the right boundary of an empty word. For a configuration-level simulation invariant, initialize the boundary tag accordingly and preserve it on stationary or suppressed outward moves. |
| Constant predicate through `exists_cond` | Constant true selects exactly `M₁` on the original input; constant false selects exactly `M₂`. A diverging unselected branch has no effect. The hypothesis on `D` prevents an unrelated semantic predicate from being substituted. |
| The decider emits its bit long before halting | Append-only singleton output forces exactly one emission over the entire run. The register keeps that bit while simulation continues until `D` halts, so early output neither escapes to the real output nor starts the branch prematurely. |
| `w₀=u=v=[]` in `computesFunInTime_ifEq` | The prescribed function is constantly `[]`; an immediate-halting, no-emission machine suffices with a positive constant. No claim of time-zero halting is needed. |
| Finite but empty symbol type in the time-bound bridge | At positive lengths there are no inputs, so a maximum of 0 is harmless. At length 0, the empty input still has a witnessed halting time. |

In particular, the conditional rewind is correct as literally described. If the input length is `n` and the head initially has position `j∈{0,…,n+1}`, after its first left move it is at

\[
q=\max(j-1,0),\qquad 0\le q\le n.
\]

For this range, a symbol is read exactly when `q>0`. The loop decrements to 0 and the final right move reaches 1. For `n=0` the first move already reaches 0, so the same argument applies. A finite sanity check also verified all 2,210 length/position combinations with `0≤n≤64`; the displayed argument establishes the general case.

For partial composition, the buffer head after phase one is on the blank immediately after the written word. The rewind must first move left; testing the current blank before that move would incorrectly stop at the right end. For a nonempty buffer, an actual move onto a blank identifies the boundary by its direction of arrival; once there, the simulator retains that boundary tag and suppresses outward moves. For an empty buffer the initial tag is right, and an inward left move reaches the adjacent left boundary. These are finite-control details of the stated clamping requirement, not additional totality or computability hypotheses. The iff promises equality of completed relations; it does not expose the construction's buffering discipline or emission timing as a separate observable guarantee.

“Some completed output” is exactly the required halting condition. For each fixed input and time,

\[
\begin{aligned}
&\exists w,\ M.\mathrm{ComputesInTime}\ x\ w\ t\\
&\qquad\iff
\bigl(M.\mathrm{tm}.\mathrm{runFrom}(M.\mathrm{tm}.\mathrm{initCfg}\ x)\ t\bigr).\mathrm{state}
=\mathrm{none}.
\end{aligned}
\]

The forward direction projects the state component of `ComputesInTimeAndSpace`. For the reverse direction take the run's actual finite output list as `w` and its defined natural-valued `spaceUsed` as the existential space witness. This uses no extra termination or output-bound theorem.

Off-image totalization is immaterial to this reduction because every query is a self-pair. It is not immaterial to all downstream statements: for example, `HALT c []=false` is a convention-dependent equality. A downstream client using arbitrary strings must keep the convention or establish that its inputs are genuine pairs. The paired unfolding lemma uses only injectivity to identify its existential pair components; it does not require an in-model inverse-pairing machine. Its dependency on the existing `pairEncode_injective` sorry is real and sufficient.

For the bound bridge, choosing times `τ(x)` permits the explicit mathematical bound

\[
T(n)=\max\bigl(\{\tau(x):x.\mathrm{length}=n\}\cup\{0\}\bigr).
\]

The finite-vector argument justifies this maximum. Since `τ(x)≤T(x.length)`, `ComputesInTime.mono` supplies the required time-bounded computation. This construction invokes a bound as a mathematical witness, not as a runtime oracle.

The numerical defect in the diagonal-pairing sketch has a direct step count. Use a controller that emits each first-pass bit once while staying put and a second time while moving right; emits the separator in two stationary steps; performs the specified rewind; then copies the input and halts. Its cost on length `n` is

\[
\underbrace{2n}_{\text{doubled first copy}}
+\underbrace{2}_{\text{separator}}
+\underbrace{(n+2)}_{\text{rewind through left blank, then right}}
+\underbrace{n}_{\text{second copy}}
+\underbrace{1}_{\text{halt}}
=4n+5.
\]

For example, at `n=10` this is 45, whereas the sketch claims 36. More generally, its output already has `3n+2` bits, and a separate nonemitting rewind costs at least `n` steps, so a `3n+6` bound cannot account for the described schedule for all lengths. Replacing that sentence by `4n+6` is safe, and

\[
4n+5\le 6(n+1)\qquad(n\ge0)
\]

establishes the current theorem's existential linear bound. No statement strengthening, weakening, or new API is needed.

Repository attestations were assessed separately from the mathematical audit. The [audited commit](https://github.com/Shilun-Allan-Li/tcslib/commit/49d25a273e89bcfa8af9e9e89ec61d1d910c358a) has exactly the stated gate commit as its sole parent. Git blob hashes of the three new modules and the three modified pre-existing modules match their copies in the attachment. Reversing the commit patches and comparing comment-free, nonblank Lean lines confirms that the changes to `Finite.lean`, `Composition.lean`, and `Encoding.lean` are insertions only; every carried sorry theorem block in those files is textually unchanged. The commit changes no other previously audited Lean implementation module, and it adds the new facade and its root export. Counting comment-free sources gives 21 sorries: precisely the seven listed new ones plus the fourteen carried ones. The carried fourteen are `computesFunInTime_const`, `computesFunInTime_comp`, `alphabet_reduction`, `one_work_tape`, `nonnegative_heads`, `oblivious_of_mem_DTIME`, `timeConstructible_id`, `PAL_mem_DTIME_linear`, `pairEncode_injective`, `exists_effectiveMachineCode`, `exists_codeTM`, `universal`, `universal_quadratic`, and `timed_universal`.

Lean and Lake are unavailable in this environment, so the zero-error elaboration attestation was not independently reproduced. The source and commit evidence corroborate the additive-change and sorry-count attestations; they are not build evidence. No source files were changed and no repository write was performed.

The findings table follows. Notes record specific dispositions and proof obligations, not blanket approval.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Encoding.lean · computesFunInTime_pairEncode_diag`, proof sketch | The asserted `3n+6` runtime does not bound the described two-pass construction. The theorem's existential linear bound remains sound. | One output bit per transition makes the doubled pass cost `2n`; separator, rewind, second pass, and halting give the explicit `4n+5` schedule above. At `n=10`, the claimed bound is 36 whereas that schedule takes 45. | Replace the numerical sentence with a bound such as `4n+6`, explicitly charging two emission steps per first-pass bit; retain the theorem statement. |
| 2 | note | `Diagonalization.lean · UC`, `UC_not_computable` | The arbitrary-`MachineCode` generalization survives the noncomputable-meaning attack. | Normalization and relabeling produce a coded hypothetical total decider; its fixed code round-trips and gives `UC=false ↔ UC=true`. No runtime encoding or decoding occurs. | No effectivity hypothesis should be added for this argument. Fill the declared normalization and encoding dependencies. |
| 3 | note | `Composition.lean · exists_comp_partial` | The iff expresses the required partial sequential composition and excludes vacuous divergence when both component runs halt. | The intermediate output is unique; either component's divergence removes all completed composite outputs, while two completed runs force a composite witness. Self-composition and empty intermediate output introduce no false statement. | Retain the untimed contract. In the construction proof, include the initial left move when rewinding and the virtual-boundary initialization and clamping invariant described above. |
| 4 | note | `Composition.lean · exists_cond` | The semantic predicate is adequately connected to the controller, and the register/rewind construction handles early emission and empty input. | `hD` forces one total singleton-output computation per input. The head calculation `j ↦ max(j−1,0) ↦ 0 ↦ 1` proves the rewind from every valid head position. | No additional condition on `p` is needed. Preserve the register until halting and initialize the selected branch with fresh work tapes. |
| 5 | note | `Computable.lean · Computes.exists_computesFunInTime` | An arbitrary length bound suffices for the normalization used here. | Finite maxima and `ComputesInTime.mono` provide the bound; `one_work_tape_binary` imposes no regularity condition on it. Empty alphabets cause only vacuous positive-length cases. | No monotonicity or constructibility hypothesis is needed. |
| 6 | note | `Halting.lean · HALT`, unfolding lemmas | Totalization and unfolding orientations are correct, with a genuine inherited injectivity dependency. | A halted run supplies its finite output and exact space witness. On a genuine pair, `pairEncode_injective` identifies the existential components; on `[]`, HALT is false by convention. | Retain the convention; downstream uses on arbitrary strings must not silently discard it. Keep the inherited sorry dependency visible. |
| 7 | note | `Halting.lean · UC_computable_of_HALT_computable`, `HALT_not_computable` | The new API closes the prior guarded-composition interface gap for this reduction. | The construction uses the self-pairing machine, three partial compositions, the fixed-word comparator, the constant machine, and one conditional. The positive HALT witness makes the universal forward clause sufficient. | No additional machine-construction theorem is needed for assembly. The component construction sorries still require proofs. |
| 8 | note | Audit header · additive-change, sorry-count, and build attestations | Source-history checks support the first two attestations; elaboration remains independently unverified. | Direct parent relation, six matching module blob hashes, insertion-only comment-free changes, unchanged carried sorry blocks, and the `14+7=21` count were checked. Lean and Lake were unavailable. | Retain build output from the pinned toolchain when filling proofs; do not equate this audit or a sorry-accepting build with completed correctness. |

Notation glossary: `M(x) ↓ w` means `∃ t, M.ComputesInTime x w t`; `Mα` is `(c.decode α).toFinTM`; `c` is the fixed coding scheme. `N` is the coded hypothetical UC decider and `α₀=c.encode N`. `D` is the hypothetical HALT decider, `U` one fixed universal-machine witness, `P` the self-pairing machine, `D'` the resulting decider for the diagonal predicate `p`, `r` the fixed-word postprocessor, `Mt` the evaluator/postprocessor branch, `Mf` the constant-true branch, and `R` their conditional composite. `w₀,t₀` are a completed decoded output and its witnessing time; `z` is a candidate composite output. `n` is input length; `j,q` are input-head positions before and after the first rewind move; `τ(x)` is a chosen halting time and `T(n)` its finite maximum at length `n`. Other names and symbols are those of the audited declarations.
