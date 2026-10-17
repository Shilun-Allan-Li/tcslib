# Diagonal Part 1 — external statement audit

**Input SHA-256:** `8e4448c3f8e030876e2d5c56107af492dfbd0a7cb7f18f588d61617f1b8863c8` — verified.

**Verdict: PASS — 0 blockers, 0 majors, 2 minors.** The parameterization preserves the received surface, is non-vacuous, and admits the intended two-tape instance. Both findings concern evidence checkers; neither identifies a defect in the submitted Lean statements or an actual duplicated proof. Repair them in the closing commit and record the results, as permitted for minors by `workflow.md` §3.

The audited target is the 536-line file supplied as `audits/evidence/diagonal-p1/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean.txt`, SHA-256 `ec8175f13eebb0b963c9c5d5bb1341eae01d6e02db3c0e221c35054d6b87eeda`.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| m1 | minor | `audits/evidence/diagonal-p1/scripts/names.py` · component screen | The screen does not establish its claimed absence of every new name throughout the base tree. | Its negative lookbehind excludes a preceding dot. In a two-file synthetic tree, `def DiagSimulator := 0` correctly fails, but `def Complexity.TimeHierarchy.DiagSimulator := 0` returns exit 0 and `NAMES: PASS`. The latter would collide with the new structure if imported together. | Allow a component to follow a dot, or match fully qualified identifiers using namespace-aware parsing. Add negative controls for fully qualified declarations and references. Re-run against the complete base and final landing trees; `tipcheck.py`'s import-closure conditions do not establish that a whole-tree name screen remains valid after unrelated files change. |
| m2 | minor | `audits/evidence/diagonal-p1/scripts/copy-text-screen.py` · declaration identity | The screen cannot detect the most relevant potential copy: the generic proof retained alongside its same-named received proof. | It identifies declarations by `(basename, unqualified name)` and skips equal pairs. Restoring the received `Complexity.time_hierarchy_of_pos` proof from the base, while retaining `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy_of_pos`, leaves the reported result unchanged: 16 pairs, 3,277 reproduced characters, zero new pairs. | Give each declaration a unique identity including its full path, namespace and source position; skip only the same declaration. Add the restored-proof mutation as a negative control, and regenerate the baseline, target and delta logs. |

These are minor checker defects, not duplication debt. Inspection of the actual target confirms that the received proofs were removed and replaced by the four one-line instances. The 16 reported pairs themselves reproduce exactly and concern unchanged clock/prefix material. No new copied-material family requires human acknowledgment.

## Evidence checked and limits

- Extracted all **64 sections**, with no repeated section path. All **38 supplied items** covered by the embedded `SHA256SUMS` match after removing bundle fences and preserving original final newlines. The manifest also names `BUNDLE-FILES.txt`, which is not included; the bundle's actual section inventory was checked directly.
- The received `Diagonal.lean` matches the generator's pinned SHA-256, `ab89c9578b230a19c127c9f3508bad453e01c79c9afb3f52e712336c5fb5ef17`.
- Independently compared all ten received declaration heads, without using `decls.py`; all are byte-identical. The six retained declaration bodies and the copyright/import/options header are also identical. The supplied freeze checker agrees.
- Rebuilt the target with `mklanded.py`, and independently applied the supplied patch with zero fuzz. Both reproduce the delivered target byte for byte.
- Reproduced the width/hygiene checks: **536 lines, maximum width 95**, unchanged imports/options, and no admission in the target code.
- Re-ran the seven-file copy screen before and after; both outputs exactly match the recorded results. Then tested the two mutations described above.
- Checked that the supplied axiom log names exactly the target's **24 explicit top-level declarations**, with only the standard axioms reported. The two simulator structures' clauses match the earlier probe, ignoring comments and whitespace.

**Execution limit:** this environment has no `lean` or `lake` executable, and the bundle does not contain the complete repository or olean snapshot. I did not independently re-elaborate Lean, re-run the 723-file name screen, or verify the complete 11-module downstream closure. The Lean and full-tree results remain supplied execution evidence. The packet's elaboration is at base `cd450a52`, with a source-graph precheck at `c9cc485b`; it is not a fresh kernel replay at the user-described campaign commit `fba93e7e`. Retain the planned fresh replay at the actual landing tip.

The reference comparison used the retrieved authors' draft text of [Theorem 3.1 and its proof](https://theory.cs.princeton.edu/complexity/book.pdf), and the authors' [model chapter, Theorem 1.9 and its relaxed proof](https://www.cs.princeton.edu/courses/archive/fall07/cos433/modelchap). These are primary-source drafts; I do not claim to have independently checked the printed edition's pagination. Tactic correctness was outside this audit; proof bodies were inspected for movement, dependencies and preservation.

## Definition and public-surface review

The following restatements come from the formal signatures and bodies. They agree with the declaration prose, subject to the explicitly discussed model conventions.

| New definition or structure | Mathematical content and assessment |
|---|---|
| `diagLangOf W g` | The complement of the inputs on which `W` completes with exactly `[true]` by time `g(|x|)`. A timeout, nontermination, or another completed output therefore belongs to the language. This exactly generalizes the received `diagLang`. |
| `DiagSimulator Φ` | One fixed finite machine `W`; for every time bound `T` and every language `L ∈ DTIME T`, constants `A,N₀` exist such that at each length `n ≥ N₀`, at least one length-`n` input makes `W` complete with the correct membership bit for `L` within `A·Φ(T(n),n)`. The constants precede `n`; the witness input may depend on `T,L,n`. This is a sufficient diagonal-simulation hypothesis, not an assertion of full universal simulation. |
| `DiagSimulator.mono` | Retains `W` and replaces its overhead by `Φ′` when `Φ(t,n) ≤ K·Φ′(t,n)` everywhere. The simulation constant changes from `A` to `A K`. Positivity of `K` need not be added: `K=0` would require an uninhabited zero-overhead source interface. |
| `SelfSimulator Ψ` | One fixed finite machine `W` and a code-indexed machine family `decode`. For each code, a constant independent of input, verdict and time transports completed one-bit runs on `pairEncode α w` to runs of `W` on that **same whole input**. Separately, every `DTIME T` language has one coded decider working on **all inputs** within `c(Ψ(T(n))+1)`. Neither computability nor surjectivity of `decode` is needed for this diagonal interface. |
| `SelfSimulator.toDiagSimulator` | Retains `W`; uses a fixed normal-form code and suffix padding to realize every sufficiently large length, giving overhead `Ψ(t)+n+1`. No padding property of `decode` is assumed. |
| `oneTapeSelfSimulator` | Takes `W=diagSim` and `decode α=(code.decode α).toFinTM`. The existing universal simulation and one-work-tape binary normal form provide `Ψ(t)=(t+1)²`. This is a concrete inhabitant, not an additional hypothesis. |
| `sqDiagSimulator` | Applies input padding to that inhabitant and weakens the overhead using `(t+1)²+n+1 ≤ 2(t+n+1)²`. Its machine remains definitionally `diagSim`. |

The two constructors simply package their fields. `DiagSimulator.W`, `.simulates`, and `SelfSimulator.W`, `.decode`, `.simulates`, `.normalForm` project exactly the data and propositions above. Thus the review covers all **14 explicit new declarations plus the 8 listed constructors/projections**.

| New theorem | Assessment |
|---|---|
| `diagLang_eq_diagLangOf` | The unchanged received definition equals its generic specialization by reduction. |
| `diagLangOf_mem_DTIME` | For every finite `W`, a time-constructible budget gives membership in `DTIME(g+1)`. No halting or simulator hypothesis on `W` is needed: `clockTM_spec` bounds the simulation of `W`'s own steps. |
| `DiagSimulator.diagLang_not_mem_DTIME` | The unbounded-length domination hypothesis intersects the simulator's eventual set of witness lengths. At such an input the correct membership bit contradicts the diagonal definition and deterministic output uniqueness. Neither time constructibility of `g` nor `hΦ` is needed here. |
| `DiagSimulator.time_hierarchy` | Adds the upper bound and class inclusion. The domination hypothesis at `A=1`, together with `t≤Φ(t,n)`, bounds `f` by `g` eventually; the positive `g+1` absorbs finitely many exceptions. |
| `DiagSimulator.time_hierarchy_of_pos` | Uses `g+1≤2g` pointwise when `g` is positive, so the larger class can be written `DTIME g`. |
| `le_sq_overhead` | The natural-number inequality `t≤(t+n+1)²` holds also at `t=n=0`. |
| `sqDiagSimulator_W` | Its conclusion is definitional equality, not merely behavioral equivalence. |

For completeness, the retained definitions still choose an effective coding scheme (`code`), choose its universal machine (`univTM`), compose prefix duplication with it (`diagSim`), and complement bounded true-output computations (`diagLang`). Their bodies did not change.

There is one harmless inherited difference from the textbook's displayed diagonal algorithm: the book chooses rejection on timeout, whereas `diagLangOf` accepts on timeout. The diagonal contradiction only uses a successfully simulated one-bit decider before the deadline, so the fallback choice has no effect. The target states its fallback semantics explicitly and preserves the received choice.

## Adversarial instances

These are mathematical checks against the literal interfaces, not newly kernel-checked lemmas. The model admits a constant decider with zero work tapes and one transition that emits `b` and halts. Consequently both the empty and universal languages belong to `DTIME(fun _ => 1)`.

1. **`Φ(t,n)=0`: impossible.** Apply `S.simulates` to the empty language with `T(n)=1`. At `n=N₀` it supplies an input with

   \[
   S.W.\mathrm{ComputesInTime}(x,[\mathrm{false}],A\cdot0),
   \]

   contradicting `FinTM.not_computesInTime_zero`. The growth hypothesis alone does **not** reject this overhead: it becomes `0≤g(n)`. The simulator contract rejects it; the hierarchy theorem's `hΦ` additionally fails at `t=1`.

2. **`W` never halts: impossible for either interface.** The same constant language forces a completed output in `DiagSimulator`. A `SelfSimulator` would produce such a diagonal simulator through `toDiagSimulator`. Although `diagLangOf W g` itself is then the universal language, the upper-bound theorem remains correct and no hierarchy theorem can use this `W` without an impossible simulator witness.

3. **`decode` constant: impossible.** If every code denotes one machine `M`, apply `normalForm` separately to the empty and universal languages at `T(n)=1`. On the same input `[]`, `M` must complete with both `[false]` and `[true]`, at possibly different times. `ComputesInTime.output_unique` gives `[false]=[true]`, a contradiction. Codes may repeat machines, but the whole decoder cannot collapse this way.

4. **`Ψ(t)=0`: impossible, despite the `+1`.** Suppose `S : SelfSimulator (fun _ => 0)`. Then `S.toDiagSimulator` has overhead `n+1`. By `timeConstructible_two_pow` and the generic upper bound,

   \[
   \operatorname{diagLangOf}(S.W,n\mapsto2^n)
   \in\operatorname{DTIME}(n\mapsto2^n+1).
   \]

   The supplied `eventually_poly_le_two_pow A 1` gives, for every `A`, eventually `A(n+1)≤2^n`. Apply the generic lower bound with `T(n)=2^n+1` and `g(n)=2^n`; its hypothesis holds independently of `T`, so the same language is **not** in that same class. Contradiction. This uses the lower-bound theorem, which does not require `hΦ`.

5. **`T(n)=0`: harmless vacuity.** `DTIME_eq_empty_of_exists_zero` gives `DTIME T=∅`; more generally one zero value suffices. Thus the simulation implication for this particular `T` is vacuous and the lower-bound conclusion is automatic. Other positive time bounds still constrain the interface.

6. **Zero constants and the empty input: no missing positivity hypothesis.** A successful simulation witness cannot have `A=0`, and a normal-form witness cannot have `c=0`, by the zero-step lemma. A per-code `C=0` is allowed only when that code has no relevant completed one-bit self-runs; such an unused code is harmless. If `g(0)=0`, no machine returns a bit at zero steps, so `[]` belongs to `diagLangOf W g`; the clock still has an `O(g+1)` budget. The positive-bound theorem explicitly excludes this case.

## Fit for the intended two-tape instance

**The verdict-only clause has the right generality.** `normalForm` supplies exactly `[b]`; the contradiction uses exactly that completed verdict. Neither forwarding longer outputs nor reflecting nontermination is needed. U2-U's full-output clause implies the required clause by specializing to `[b]`, and

\[
C(t+1)\le C(t+|\operatorname{pairEncode}(\alpha,w)|+1).
\]

The added input-length allowance also admits the existing prefix-copying simulator. It does not prevent the book-strength conclusion once `n≤f(n)` is imposed.

**The `+1` in the normal form is harmless.** For `n≥2|α|+2`, choose `w` of length `n-(2|α|+2)`. Then

\[
|\operatorname{pairEncode}(\alpha,w)|=2|\alpha|+2+|w|=n,
\]
\[
C\bigl(c(\Psi(T(n))+1)+n+1\bigr)
\le C(c+1)\bigl(\Psi(T(n))+n+1\bigr).
\]

Both constants are fixed before choosing `n`. Thus padding provides the exact quantifier order required by `DiagSimulator`.

For `Ψ(t)=(t+1)(Nat.log 2 (t+1)+1)`, the probe supplies constant-factor absorption under `t↦c₀t` and derives the book form from a `SelfSimulator Ψ`. For `2≤n≤f(n)`, its arithmetic yields

\[
\begin{aligned}
\Psi(f(n))+n+1
&\le2(f(n)+n+1)\bigl(\lfloor\log_2(f(n)+n+1)\rfloor+1\bigr)\\
&\le24f(n)\lfloor\log_2 f(n)\rfloor.
\end{aligned}
\]

The generic structures therefore accept the planned G5 normal form and U2-U simulator without strengthening their contracts. The probe's actual assembled witness uses its deliberately sorried verdict-only U2-V row; it does **not** establish U2-U. Replacing that row by the stronger proposed U2-U statement is immediate at the interface level. Construction and proof of U2/G5 remain outside this gate.

`hΦ : ∀ t n, t≤Φ(t,n)` is sufficient, but not minimal: for the inclusion argument an eventual constant-factor comparison along `f` would suffice. The current interface is simple and fits both intended instances. I recommend keeping it; the sparse agreement clause of `DiagSimulator` should not itself be mistaken for a full-input simulation proving class inclusion.

## Preservation, movement and consumers

All **ten received heads** are byte-identical. `code`, `univTM`, `univTM_spec`, `diagSim`, `diagLang` and `diag_cost_le` retain their bodies. The only four replaced proofs are:

| Received theorem | Exact new proof term |
|---|---|
| `TimeHierarchy.diagLang_mem_DTIME` | `diagLangOf_mem_DTIME diagSim hg` |
| `TimeHierarchy.diagLang_not_mem_DTIME` | `sqDiagSimulator.diagLang_not_mem_DTIME hT` |
| `Complexity.time_hierarchy` | `sqDiagSimulator.time_hierarchy le_sq_overhead hg hfg` |
| `Complexity.time_hierarchy_of_pos` | `sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg` |

The upper-bound argument moved into `diagLangOf_mem_DTIME`; the contradiction, inclusion and positive-bound conversion moved into the corresponding `DiagSimulator` lemmas. The former lower-bound proof's machine preparation was separated into `oneTapeSelfSimulator` and input padding into `toDiagSimulator`. The received theorem bodies no longer contain those proofs. The unused public arithmetic lemma is retained for compatibility, not copied anew.

| Importer | Source-level dependency and conclusion |
|---|---|
| `TimeHierarchy/Separation` | Uses the preserved diagonal language and the preserved upper, lower and positive hierarchy statements. No edit indicated. |
| `Diagonalization/EXPCOM` | Imports the module; references the coding pattern in prose. No changed dependency. |
| `Diagonalization/NotTimeConstructible` | Uses the unchanged `TimeHierarchy.code`. No edit indicated. |
| `SpaceComplexity/Hierarchy` | Uses the unchanged `TimeHierarchy.code`. No edit indicated. |
| `TimeHierarchy` facade | Imports `Diagonal` and `Separation`; its quadratic-overhead description remains true. No edit indicated. |

The cut-check construction includes the proposed target's body and isolates module-local sections. Its supplied results report identical baseline/cut message counts **9, 1, 8, 6, 0**, respectively, and no errors. Existing `sorryAx` dependencies in EXPCOM and the space hierarchy are visible in those logs; they are not dependencies introduced into Part 1. The unchanged public surface, direct source uses and cut evidence support the no-edit conclusion, subject to the execution limit stated above.

## Rulings on the pack's questions

1. **Field `W`: keep it.** It follows the existing `clockTM K W` convention, is explicitly documented, and does not violate a naming rule in the supplied policy. Renaming it to `sim` offers no necessary correction.
2. **Unused `diag_cost_le`: keep it in Part 1.** The authorization requires preserving the public surface. Its changed docstring accurately explains its status. Any later retirement should be a separate, explicitly authorized compatibility decision; this gate does not recommend deleting it now.
3. **Verdict-only `SelfSimulator.simulates`: keep it.** It is sufficient, admits the proposed full-output U2-U instance, and avoids an unnecessary output requirement. This abstract field does not introduce the separate verdict-only universal-machine row that the user declined to land.
4. **Facade sentence: leave it unchanged in Part 1.** The named `Complexity.time_hierarchy` still has the received quadratic hypothesis. Revisit the headline description when book-strength corollaries actually land.

The source-derived generic results carry AB09 references and the nontrivial arguments have matching sketches. The identity, arithmetic and transport helpers fall under `policy.md` §2's exception for technical glue; the pack's blanket wording about tags should be understood with that policy exception. The proposed change touches only the authorized mathematical file.

## Suggested permanent sanity checks

Add small, compiled checks when convenient; they are not additional conditions for this statement gate:

- `¬ Nonempty (DiagSimulator (fun _ _ => 0))` and `¬ Nonempty (SelfSimulator (fun _ => 0))`, following the arguments above.
- A `SelfSimulator` cannot have a constant `decode` function.
- Machine-projection identities for `DiagSimulator.mono` and `SelfSimulator.toDiagSimulator`, both by `rfl`.

Separately, the two checker mutations in m1–m2 should become required negative controls. Re-screen the final tree and perform the already-planned downstream Lean replay before integration.

## Notation

`W` is the simulator machine; `S` is a bundled simulator; `Φ(t,n)` is padded simulation overhead; `Ψ(t)` is normal-form overhead. `f,g,T` are time bounds; `L` is a language; `α` is a code; `x,w` are binary strings; `n` is input length; `t` is a step budget. `A,C,c,c₀,K` are natural-number constants; `N,N₀` are length thresholds; `[b]` is the singleton output containing Boolean `b`. `|x|` denotes string length, and the floored base-two logarithm denotes `Nat.log 2` on positive arguments. `DTIME` and `TimeConstructible` have the supplied repository definitions.
