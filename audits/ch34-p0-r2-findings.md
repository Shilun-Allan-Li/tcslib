Input SHA-256, independently recomputed: `cb809b78da0fa2c308158c6722bdf8606bb7c002cd18f50c937b2b3f34cabb8d`.

Confirmed: **10 top-level attachments**, with distinct paths; 1,591,987 input bytes.

**PASS — the P0 reception gate closes: 0 blockers, 0 majors, 3 minors.** The open minors are the remaining part of round-1 finding 6 and new findings 11–12 below. Round-1 finding 1 is closed. Findings 2–5, 7, and 8 are closed; notes 9–10 remain unchanged and frozen.

Date: 2026-10-08. Scope: the P0 repairs in `84b79daf..2ca970cd`, including the nine S1–S6 statements in `ZeroSpace.lean` and S9 in `CounterProgRun.lean`. All ten new in-scope theorem statements are mathematically true. They remain admitted statements; this is not a proof-fill certification. The phase-P3.1/P4.1 statements and the design-document §12 addendum were not audited. I read the definition of `evenLang` solely to determine what S6 asserts.

**Findings table**

Paths below are relative to `TCSlib/Complexity/`, except the plan. Line numbers refer to the reconstructed right-endpoint files, not the enclosing bundle. Existing numbering is preserved.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 6 | **minor — partially repaired** | `SpaceComplexity/Machines/ParseCmp.lean:302–305` · `ReachesB`, new reference to `Reaches.toB` | Consumers needing an inclusive bound are directed to `Reaches.toB` as an example of adding the final-configuration hypothesis. | The new description of `ReachesB` itself is correct. However, `Reaches.toB` assumes a bound on the fixed **pre-final** coordinate `p` and concludes only `ReachesB`. It does not bound the reached configuration. With `T=0`, `p=L=0`, and a configuration whose selected head is at `2`, its premises hold and the reached head remains outside `[-1,0]`. See the explicit instantiation below. | Remove the misleading reference, or describe `Reaches.toB` as converting a fixed pre-final coordinate bound into a pre-final interval bound. For an inclusive bound, separately require `-1 ≤ c₁.workTapePos r ∧ c₁.workTapePos r ≤ L`. Correct the adjacent `Reaches.toB` docstring's “ending with” wording when making this local documentation repair. No theorem change is needed. |
| 11 | **minor — new** | `SpaceComplexity/ZeroSpace.lean:20–21`; `AroraBarakChapters3-4Plan.md:155–156` | The normalization statements are already “machine-checked facts” / “machine-checked” identities. | Every one of the nine `ZeroSpace` declarations ends in `sorry`; the supplied log records nine corresponding admission warnings. Their propositions have been elaborated according to the log, but their truth has not been established by completed Lean proofs. The pack correctly discloses this elsewhere. | Say “elaborated sanity statements, with proofs deferred to fill,” reserving the proof-completion claim until the admissions are discharged. This is a wording correction, not a request to fill proofs at this gate. |
| 12 | **minor — new** | `SpaceComplexity/ZeroSpace.lean:162,179` · `trueLang_mem_SPACE_zero`, `evenLang_mem_SPACE_zero` | S6 supplies round 1's requested witnesses “with the stated space and time contracts.” | Both memberships are true. Unfolding `SPACE` and applying S2 also recovers zero-work-tape witnesses. But neither signature constrains the halting time: `ComputesInSpace` only supplies an unspecified existential time for each input. The one-step constant computation and the `x.length + 1` parity computation appear only in the sketches. | Add witness statements retaining the time contracts: a zero-tape machine computing `[true]` within one step on every input, and a zero-tape machine deciding `evenLang` within `x.length + 1` steps. Keep the existing membership corollaries. Their proofs may remain fill obligations, as authorized for this round. |

Finding 11 uses the ordinary Lean distinction between an admitted statement and a completed proof: `sorry` introduces `sorryAx`. See the official [Lean proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/). The admissions themselves are permitted by this audit's brief.

**Disposition of every round-1 item**

| Round-1 # | Disposition | Repair check |
|---|---|---|
| 1 | **Closed** | The frozen `SPACE` definition is unchanged. `Basic.lean` documents the single-zero collapse. Plan §2.4 adopts positivity at every length; §1 explicitly changes Exercise 3.2 to `SPACE(n+1) ≠ NP`. S1–S4 state the required characterization and normalization identities exactly. S5 and the space part of S6 are also sound. Finding 12 does not affect the normalization repair. |
| 2 | **Closed** | The `sim_run` declaration's headline now states the initial `t`-step headroom condition. Its original signature and proof are unchanged. The new S9 interface retains the input-position hypothesis and uses bounds at every abstract time strictly less than `t`. Its `t(2B+5)` conclusion is valid; see below. |
| 3 | **Closed** | Both the main-definition description and the `Mode` constructors now require at least one argument for the guaranteed pair shape. The zero-argument behavior is preserved. |
| 4 | **Closed** | `valP` now specifies a canonical `Nat.bits` payload; `valQ` specifies two canonical inner payloads. These match `ValidPlain` and `ValidPair`. The named rejection of `pairEncode [] [false]` is correct. |
| 5 | **Closed** | Both length-comparison docstrings now describe the default projections and malformed-word membership. This matches `pairFstD` and `pairSndD`, which both return `[]` when decoding fails. The theorem statements are unchanged. |
| 6 | **Partially repaired; minor remains** | The strict-before-final-time wording and the zero-step example are correct. The new reference to `Reaches.toB` misidentifies what that lemma supplies; see finding 6. |
| 7 | **Closed for the replacement evidence** | The new sweep records full revision `2ca970cd513c10dc413d8e0847874fc0fa0516ac` at its start, matching the repair diff's stated right endpoint. Its module and admission counts reconcile with the supplied source. The old `e64cec9e` relationship is now explicitly an erratum; its independent verification is unnecessary to use this replacement sweep. Evidence limits are recorded below. |
| 8 | **Closed** | Every newly listed `ARMSim.sim_*` result exists; `arm_run` exists in `ARMRun`. Singular `CallOK` and its use in both compilation theorems' `hcalls` hypotheses match the correction. `Sim`, `CallReturn`, and `Call` are supplied modules with the advertised roles. |
| 9–10 | **Frozen; no change required** | The time-hierarchy strength and the limitations on general implicit composition were not re-audited. |

**S1–S6: statement truth and delivered strength**

The following are mathematical derivations from the received definitions and interfaces, not newly elaborated Lean proofs.

S1. For every work tape `j`, time zero lies in `Finset.range (t + 1)`. Its image under the head-position function therefore contains the initial head position, which is zero. Thus

\[
\begin{aligned}
0&\in\operatorname{visitedByTapeHead}(M,x,t,j),\\
1&\le\left|\operatorname{visitedByTapeHead}(M,x,t,j)\right|,\\
M.k=\sum_{j:\mathrm{Fin}(M.k)}1
&\le\sum_{j:\mathrm{Fin}(M.k)}
\left|\operatorname{visitedByTapeHead}(M,x,t,j)\right|
=\operatorname{spaceUsed}(M,x,t).
\end{aligned}
\]

This includes `t=0` and `M.k=0`. The received `Clean.visited_interval` interface independently confirms origin membership. No halting hypothesis is needed for S1.

S2. Given `s n₀ = 0`, instantiate the total computing contract at `x = List.replicate n₀ false`. Since `x.length = n₀`, some halting time satisfies

\[
0\le M.k\le\operatorname{spaceUsed}(M,x,t)\le s(n_0)=0.
\]

Hence `M.k = 0`. This concerns one fixed machine for every input, not a different machine at each length. The restriction to binary inputs makes a word of every natural length available.

S3. If `L ∈ SPACE s`, take its witnesses `c,M`. A zero of `s` is also a zero of `fun n => c * s n`, so S2 forces `M.k=0`. Consequently, on every input and at every time,

\[
\operatorname{spaceUsed}(M,x,t)
=\sum_{j:\mathrm{Fin}(0)}\left|\operatorname{visitedByTapeHead}(M,x,t,j)\right|=0.
\]

The same machine and halting times witness membership in `SPACE (fun _ => 0)`. Conversely, a zero-space contract weakens to `c * s n` because that bound is nonnegative. Both inclusions hold, including when `c=0`. The identity-bound instance follows by choosing `n₀=0`.

S4. For everywhere-positive natural-valued `s`,

\[
s(n)\le s(n)+1\le2s(n),\qquad
c(s(n)+1)\le(2c)s(n).
\]

Monotonicity gives one inclusion, and replacing the existential constant `c` by `2c` gives the reverse inclusion. For arbitrary `s`, the corresponding inequalities are

\[
\max(1,s(n))\le s(n)+1\le2\max(1,s(n)).
\]

These prove both stated identities without constructibility, monotonicity, or eventual-growth assumptions. Positivity must hold at **every** length for the first identity; eventual positivity does not suffice. The second identity deliberately compares two normalized bounds and does not equate unnormalized `SPACE s` to them.

The plan's chosen bounds meet this requirement:

\[
n+1\ge1,\qquad n^c+1\ge1,\qquad
\operatorname{logSpace}(n)=\operatorname{Nat.log}_2(n)+1\ge1.
\]

The plan's generic constructible space bounds also carry `logSpace n ≤ S n`. The revised convention is sufficient for the in-scope plan; this does not certify implementations of future or excluded phase statements.

S5. Apply `pairDecode` to the asserted equality. `pairDecode_pairEncode` gives

\[
(x,\operatorname{Nat.bits}(i))=(y,\operatorname{Nat.bits}(j)).
\]

Therefore `x=y` and the two bit lists agree. Applying the received `bitsVal` inverse gives `i=j`. Conversely, substituting those equalities gives the encoded equality. At zero,

\[
\operatorname{pairEncode}([],\operatorname{Nat.bits}(0))
=\operatorname{pairEncode}([],[])=[\mathrm{false},\mathrm{true}]\ne[].
\]

The statement has the requested scope and handles index zero correctly.

S6. `trueLang_mem_SPACE_zero` asserts membership of the full language. A machine with no work tapes, one live state, and a transition that emits `true` and halts computes the required one-bit output in one step. Its space is the empty sum, independently of input length.

Here `evenLang` means an even number of `true` bits, rather than even input length:

\[
x\in\operatorname{evenLang}\iff x.\operatorname{count}(\mathrm{true})\bmod2=0.
\]

Use two live states representing even and odd parity, initially even, and no work tapes. A `false` leaves the state unchanged; a `true` toggles it. After consuming `j` symbols, the state equals

\[
(x.\operatorname{take}(j)).\operatorname{count}(\mathrm{true})\bmod2.
\]

At the right blank, emit the indicator that this value is zero and halt. In this model the input head begins at the first symbol, so the construction consumes `x.length` symbol steps and one final step. It uses zero work cells, including on empty input. Moreover, `[]` is accepted and `[true]` rejected, so the language is nonconstant. Both S6 statements are true and imply zero-tape witnesses through S2. Their omission of the explicit time contracts is precisely finding 12. No formal regular-language equivalence is claimed or required here.

**S9 and the repaired boundary cases**

S9 is true. In fact, its hypotheses also permit the tighter bound `t(2B+3)`: the received `CounterProg.sim_step` requires only that the registers in its starting abstract state are at most `B`. It does not require the resulting registers to remain at most `B`.

To derive that bound, induct on the abstract run length. At zero, use machine time zero. If the abstract state is halted, both encodings are stationary. Otherwise, the hypothesis at `j=0` supplies `sim_step`'s register bound; `hp` supplies its input-position bound. One simulated step costs at most `2B+3`. For the suffix, `step_pos_le` preserves the position condition, and

\[
\operatorname{run}(P,x,\operatorname{step}(P,x,s),j)
=\operatorname{run}(P,x,s,j+1)
\]

transfers the remaining register bounds. Compose the physical runs using `runFrom_add`. The induction's time calculation is

\[
t_1+t_2\le(2B+3)+t(2B+3)
=(t+1)(2B+3)\le(t+1)(2B+5).
\]

Thus the supplied constant `2B+5` is conservative and sound; it need not be changed. Applying `sim_step` at `B+1`, as the sketch proposes, is also valid. No final abstract register bound is needed.

The following adversarial cases check the repair boundaries rather than reopening the frozen round-1 audit:

| Case | Result |
|---|---|
| A bound with one zero at length `7`, positive elsewhere | S2 uses the all-false word of length `7`; S3 collapses the class globally. Merely eventual positivity still fails. |
| `t=0`, one work tape | S1 charges the origin: space is at least one. Zero elapsed time does not evade the collapse. |
| `s` identically zero | S4's positive-bound premise is unavailable; its second identity correctly reduces to equality between the two constant-one normalizations. |
| Constant-register `goto` loop starting at `B`, run for a positive number of steps | The old `sim_run` headroom hypothesis fails. S9 applies because each reached register equals `B`. |
| `B=0`, `t=1`, one final increment from zero | S9's pre-step hypothesis holds; the final value is one. One machine step is within its five-step budget. |
| `t=0`, arbitrarily large register values | S9's register hypothesis is vacuous; machine time zero establishes its conclusion. |
| `whole` call, zero arguments, empty input | `vword (callSegs …)=[]`, as the revised documentation states. With one empty argument the separator appears, giving `[false,true]`. |
| `pairEncode [] [false]` | Pair decoding succeeds, but `[false]` is noncanonical, so `valP` rejects. The revised contract captures this. |
| Malformed word `[]` in either length predicate | Both projections are `[]`; `0=0` and `0≤0` hold. Both new docstrings are accurate. |
| S6 on `[]`, `[false]`, and `[true]` | The first two have even bit parity and the third odd parity. The zero-tape scanner outputs exactly one correct bit in one, two, and two steps, respectively. |

For the residual finding 6, choose one register, `r=0`, `L=0`, `p=0`, and a configuration `c₀` with `c₀.workTapePos 0 = 2`. For any reference configuration `c`, the witness `T=0` gives

\[
\begin{aligned}
&\operatorname{rrun}(P,\operatorname{oracle},c_0,0)=c_0,\\
&\forall t<0,\;\text{the required pre-final condition},\\
&\operatorname{Reaches}(P,\operatorname{oracle},c_0,c_0,c,0,0),\\
&-1\le0\le0,\\
&\operatorname{ReachesB}(P,\operatorname{oracle},c_0,c_0,c,0,0)
\quad\text{by `Reaches.toB`},\\
&c_0.\operatorname{workTapePos}(0)=2>0=L.
\end{aligned}
\]

This refutes the new reference's implication about inclusive bounds, while confirming that the repaired definition description is correct. It is a documentation counterexample, not a false-theorem finding.

**Evidence reconciliation and audit limits**

I reconstructed the embedded round-1 bundle from the diff. It has exactly 865,996 bytes and reproduces its original SHA-256, `69f84b8d7194081e3b7749467f41f2c77fc3f09409e655badac32a4ae6b3d05b`. This supplies a hash-matched baseline for the received files.

For the 28 diff entries whose baselines were supplied or which were new files, I applied the hunks with exact context checks and recomputed the Git blob hashes. Every result matches the diff's advertised hash prefix. The separately attached plan, round-1 report, and three full Lean files agree with their reconstructed versions after removing the bundle's extra separator newline. This checks internal content consistency; it does not independently authenticate the repository's commit graph.

Among the 44 received modules, eight changed only in comments. `CounterProgRun.lean` adds only the S9 declaration outside its comments. The `SpaceComplexity` facade adds the declared imports. Existing received definitions, theorem signatures, and proof bodies are unchanged. The sole direct `sorry` in the received files is S9, and there are no explicit `axiom` declarations there. This is a source comparison, not a transitive kernel-axiom audit; the facade now imports the declared statement skeletons.

The replacement sweep contains 101 distinct module entries, includes all 44 received modules, ends with `R2_SWEEP_OK 101 modules`, and has no `error:` lines. The import order is consistent for the supplied modules and their listed imports. I counted exactly 34 admission warnings, matching the reconstructed source inventory file by file: nine in `ZeroSpace`, one in `CounterProgRun`, and 24 in the excluded phase skeletons. The style log covers 35 files under `SpaceComplexity/`, has zero `FAIL` entries, and has 13 size warnings elsewhere. Their file set exactly matches the round-1 warning set and contains no received module.

There is no `lean` or `lake` executable in this environment. I did not independently rerun elaboration or lint, inspect the claimed 101 generated `.olean` files, verify that the scratch tree was wiped, or verify the original `84b79daf`/`e64cec9e` source relationship. The new log asserts the wipe and identifies the revision at start. Contrary to the pack's phrase “as the log header records,” its header does not record working-tree cleanliness or the untracked directories; those remain maintainer attestations. This does not recreate finding 7's revision mismatch, because the replacement log names the relevant revision explicitly.

The major is resolved by the documented convention and the sound statement contracts. The three listed minors can be addressed without changing the frozen `SPACE` definition or any received theorem. Proof completion and the excluded phase audits remain separate obligations.

**Notation glossary.** Mathematical displays abbreviate `M.tm.spaceUsed (M.tm.initCfg x) t` as `spaceUsed(M,x,t)` and the corresponding per-tape visited set as `visitedByTapeHead(M,x,t,j)`. `M` is a machine; `M.k` its tape count; `x,y` input words; `s,S` space bounds; `n,n₀,c,B` natural-number lengths or bounds as in the cited statements; `i,j` indices; `t,T,t₁,t₂` step counts; `P` a program; `oracle` its answer function; `r,p,L,c₀,c₁,c` in the reaching-relation discussion retain their source meanings (register, coordinate, interval upper bound, and configurations). Vertical bars around a finite set denote its cardinality. Elsewhere `L` denotes a language, and `s` in the S9 discussion denotes the abstract state, following the source signatures.
