# Pass–shelat Gate 28, round 2 — derandomization host statement audit

**Verdict: CLEAR. 0 blockers, 0 majors, 2 minors, 1 note.**

All four round-1 findings are closed for this statement gate. The new machine contract is
mathematically sound, satisfies the recorded head-envelope ruling, and implies the unchanged
decision-class corollary needed by Theorem 180.1. Two new minors concern the stale GitHub PR
description and an overstated dependency claim in the pack. A handoff note concerns the
decision-predicate reader needed by the later host proof. The host and corollary remain
intentionally admitted; this is not a proof audit.
No repository edit, PR update, dispatch, or merge was performed.

| Item | Audited revision |
|---|---|
| Draft PR | [#312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) |
| Lean head | `0c04d1eb1e5450372632a23f3e94f3b7bfc37606` |
| Round-1 Lean head | `8972fb4ef15fa3d4e3df37d6aa8674408835593d` |
| Intermediate round-2 head | `2f9333b99b83fdd6accb29926fab38fd75f66897` |
| Lean merge base | `013119f006af40d03b88b0fc2d9b453cf0a9b348` |
| Campaign records | `50416ccc67b9a28fea74177c2cb2ecf562cc6b29` |
| Exchange | `4bf496ccd5ffa48f70704251cd0310d8aa13a2fe` |
| Staged target tip checked | `c080a8406f5a8f8d29e5cf1787162d26a1d8a64c` |

## Round-1 findings

Line numbers refer to the pinned Lean head or requested records, as appropriate.

| ID | Original severity | File / declaration | Round-2 disposition and evidence |
|---|---|---|---|
| G28-01 | major | `machine-library-design.md` §14, lines 3069–3095 | **CLOSED.** H17 is in the canonical registry, not merely a draft. Its hypotheses, strict-majority language, one-machine correctness/time/envelope contract, home, reader, admitted corollary, proof owner, consumers, route, ruling, and audited head match the code. The companion status sentence is present. |
| G28-02 | major | `Randomized/SeedMajority.lean:192–203`, `Complexity.exists_seedMajorityTM` | **CLOSED.** One existential `M,c,e` binds both `M.DecidesInTime S B` and the all-input, all-time, all-work-tape head envelope with the same budget. This is the time-derived envelope authorized by the recorded ruling. No admitted space specification supplies it. |
| G28-03 | minor | `Randomized/SeedMajority.lean:72–80` | **CLOSED.** The consumer paragraph changes both the test and width: true coins with width `m(n)` below the threshold; expanded-generator output truncated to `m(n)`, with width `ℓ(n)`, from the threshold on. |
| N28-01 | note | Module, contract/corollary docstrings, facade, H17, resolutions | **CLOSED for this gate.** The `derand` fill owns the host contract, corollary, and Theorem 180.1. Updating the issued brief/checkpoint, order, and roots remains the explicitly recorded action after this gate and before dispatch; these files have not already been updated by this PR. |

## New findings

| ID | Severity | File / declaration | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| G28-R2-01 | **minor** | PR #312 description, especially lines 5, 22, 28–29, 46–50 in the captured `pr312-description.md` | The description still describes round 1: a 163-line module, a class-membership-only interface, absence of a machine contract and space clause, one admission, and the old seal/evidence. The retrieved PR head is the requested `0c04d1eb`; the code instead has 234 lines, the new machine-level envelope contract, and two intended admissions. The obsolete interface description now contradicts the implemented G28-02 repair. | Rewrite the description for the final head: identify `exists_seedMajorityTM`, the admitted corollary awaiting `mem_DTIME_iff`, the unchanged proved reader, both intended admissions, and the round-2b build/seal evidence. This is a description-only correction. |
| G28-R2-02 | **minor** | `pack-r2.md:170,216–218`, moved-base dependency record | The pack lists both root `TCSlib` and `audits/pass-shelat/Checks` as importers of both PRs. An independent import-graph traversal finds only root `TCSlib` in the common downstream set. `Checks.lean` imports the Randomized facade, but its cryptography imports do not reach `SecureComputation` or `SpecialEncryptionMulti`; its unchanged source is at lines 8–12. The pack therefore overstates the combined-tree rebuild surface. | Correct both passages: root `TCSlib` is the common importer; `Checks` reaches #312 but not #311. This does not weaken the conclusion that the changed modules are independent, or require a new Lean statement/build. |
| N28-R2-01 | **note** | `ClassP/DTIME.lean:75–77`; future `derand` host proof | The planned loop construction returns `ComputesFunInTime`, while the host conclusion uses `FinTM.DecidesInTime`. That predicate has no published general characterization at this head. `mem_DTIME_iff` exposes the class-membership existential, not the decision predicate's input/output formula. The future proof cannot simply introduce/apply `DecidesInTime` through its body under the same Rule-10 discipline that rejected the intermediate corollary. No such forbidden read is present in the final admitted bodies. | Before filling the host, arrange a published reader, e.g. `FinTM.decidesInTime_iff` beside the predicate, and record the necessary scope authorization; alternatively exhibit a public construction route avoiding that read. A separate predicate reader is not one of the two currently named pre-approvals. This is a later-fill handoff, not an additional statement-gate blocker. |

None reopens a repaired major. The host specification and the two archived builds are
unaffected by the documentation corrections or the later-fill reader obligation.

## Machine contract: truth and envelope

Write `S` for the displayed strict-majority language and
`B(n)=c·(2^{w(n)}·(n+1)^e)`, exactly as in the contract docstring.

The time/correctness argument from round 1 remains applicable. For input length `n`, let
`R=2^{w(n)}`. The unary-width hypothesis gives a fixed polynomial bound on `w(n)`. Enumerate
the `R` fixed-width binary words, maintaining the binary rank and acceptance count. With
`a_i` the count after `i` tests,

\[
a_0=0,\qquad
a_{i+1}=a_i+\mathbf 1[\operatorname{pairEncode}(x,\operatorname{word}_{w(n)}(i))\in V]
\quad(0\le i<R).
\]

Induction gives

\[
a_i=\#\{j<i:\operatorname{pairEncode}(x,\operatorname{word}_{w(n)}(j))\in V\},
\qquad 0\le a_i\le i\le R.
\]

At `i=R`, the fixed-width binary-expansion bijection identifies `a_R` with the theorem's
`Finset` cardinality. The output is the Boolean verdict `R<2a_R`. Both counters need at most
`w(n)+1` bits, including the terminal value `R`. Make the terminal step fixed, or retain the
existing size guard, so that the invariant is preserved by the total step function.

All per-round operations and initialization have a common polynomial budget `T(n)`. For
suitable fixed natural constants `A,e`, the loop bound satisfies

\[
T(n)+1\le A(n+1)^e,\qquad R+2\le3R,
\]
\[
c_0(T(n)+1)(R+2)\le 3c_0A\,2^{w(n)}(n+1)^e.
\]

Thus the advertised time normal form is attainable, including initialization and final
comparison. Fuel is **binary** `Nat.bits R`, of length `w(n)+1`. The published
`exists_loopFindTM` accepts arbitrary numerical fuel and searches through the terminal rank;
its proved body uses `loopHost_contracts`. The approved generic-fuel harvest remains needed
to reuse the private `IterateFind` adapters without copying them. This is a feasible fill
route, not a completed Lean construction.

For the new envelope, fix the resulting machine, an input `x`, and a work tape `j`. Set
`b=B(|x|)` and let `p(v)` be that head's integer position after `v` steps from `M.tm.initCfg x`.
The source definitions and published lemmas give:

1. `p(0)=0`, by `Cfg.init_workTapePos`.
2. `−v ≤ p(v) ≤ v`, by `MultiTapeTM.workTapePos_runFrom_mem_Icc`.
3. The run is halted at time `b`, by the decision/time specification and
   `FinTM.computesInTime_iff`.
4. If `b≤v`, `runFrom(init,v)=runFrom(runFrom(init,b),v−b)=runFrom(init,b)`, by
   `runFrom_add` and `runFrom_of_halt`.

Consequently

\[
|p(v)|\le
\begin{cases}v,&v\le b,\\b,&b\le v,\end{cases}
\qquad\text{hence}\qquad |p(v)|\le\min(v,b)\le b.
\]

This proves the mathematical implication from the time bound to the stated envelope for
**the same machine and constants**. It uses no `loopHostTM_*` or `timedCondTM_*` space spec.
The input configuration is the correct starting configuration for a standalone decider;
`Clean.envelope` uses a seam configuration because it concerns a clean module call. The
absolute-position bound has the same form without asserting that this decider is itself a
clean installable module. That is exactly the recorded coarse-envelope ruling.

Boundary cases remain sound. Ties reject. At `w(n)=0` there is one empty seed, and the
comparison `1<2·count` accepts exactly when that seed passes. At `n=0` the factor `(n+1)^e`
is one, and a fixed constant covers the fixed initialization cost. A witnessing `c` cannot
be zero: that would give a zero-step halting decider, contradicting
`FinTM.not_computesInTime_zero`. No sharper space bound is needed by this gate. The prose
about a sharper envelope is not a published linear-space specification; bounded state
words and polynomial-time leaf calls support a polynomial envelope in the intended route.

## Corollary, sufficiency, and Rule 10

The headers of `seedMajority_mem_DTIME` and `half_lt_randProb_iff` are byte-identical at
round 1, the intermediate round-2 head, and the final head. The reader's complete proof is
unchanged. The machine-contract header is unchanged between the two round-2 heads.

For `T(n)=2^{w(n)}(n+1)^e`, the first machine-contract conjunct is literally
`M.DecidesInTime S (fun n => c*T n)`. The approved future reader

\[
S\in\mathrm{DTIME}(T)
\iff \exists c\,M,\ M.\mathrm{DecidesInTime}\ S\ (n\mapsto cT(n))
\]

will give the corollary with witnesses `c,M` and then `e`; neither monotonicity nor constant
absorption is necessary for this step. A full source scan at the head found no existing
direct introduction reader for these inputs. `mem_DTIME_of_decidesInTimeVia` requires the
different `DecidesInTimeVia` predicate; the RAM introduction theorem requires an `XProgram`.

The intermediate proof converted the two decision predicates by their definitions. Its
stronger seal fails within that proof, as disclosed. At the final head the proof and its
two extra imports are removed. Keeping the corollary admitted until the pre-approved
`mem_DTIME_iff` is available is appropriate for this statement gate and Rule 10.
For the later host proof, the separate decision-predicate reader described in N28-R2-01
must also be addressed: the mathematical envelope argument above uses that predicate's
meaning, while a Rule-10-clean implementation must obtain that meaning through a public API.

The only completed proof in the module reads `randProb` through `randProb_eq`. Its
positive-denominator calculation is

\[
\tfrac12<\frac{\mathrm{count}}{2^m}
\iff 2^m<2\,\mathrm{count},\qquad 2^m>0.
\]

The unchanged corollary is still sufficient for the full Theorem 180.1 route checked in
round 1. The revised consumer paragraph now matches that route. In particular:

- Choose a fixed integer `d≥2` with `1/d<min(ε,1)` and the computable ceiling-root schedule
  `ℓ(n)=min{t:n≤t^d}`. Polynomial PRG expansion covers the verifier's coin width `m(n)`.
- The nonuniform-advice argument bounds the PRG acceptance gap by `1/12` at every input
  beyond some threshold `n₀`: a seed length `s` has only finitely many associated input
  lengths, each at most `s^d`. The piecewise test uses true coins below `n₀`.
- Member/nonmember probabilities beyond `n₀` are respectively at least `7/12` and at most
  `5/12`. The reader therefore identifies the language exactly with the strict majority.
- Eventually
  `log₂(2^{ℓ(n)}(n+1)^e) ≤ n^{1/d}+1+e log₂(n+1) ≤ n^ε`.
  The positive `subexpBound` absorbs the finite exceptions by one constant, then
  `DTIME.mono` and `DTIME_const_mul_subset` finish.

The consumer probe verifies only that final transport from supplied language equality and
pointwise bounds. The PRG argument, polynomial-time implementations, enumeration invariant,
machine construction, and asymptotic estimate remain obligations of the `derand` fill.
The source's exhaustive-seed argument was rechecked in [PS10, §8.2, Theorem 180.1, printed
p. 180](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf).

## Registry wording and ownership

The canonical H17 row is byte-identical at the requested records pin and the staged target
tip. Its route's explicit generic-fuel harvest and the module's reference to the existing
`polyTimeComputable_find` construction are consistent: the approved harvest exposes the
needed generic-fuel form in the same shared file. This is not permission to copy private
helpers or use the polynomial-fuel final bound on exponential fuel.

H17's status cell names the host and Theorem 180.1 without repeating the corollary; its
contract cell explicitly assigns the reader addition and corollary proof to `derand`.
Together with the module and corollary docstrings, ownership is unambiguous. No new finding.

The prose saying a proof would read `DecidesInTime`, `DecidesInTimeVia`, and `DTIME` is best
read as listing the forbidden reads in the alternative routes: the removed bridge reads
the two machine predicates, while a direct constructor reads `DTIME`. It does not mean
every possible proof must unfold all three. This imprecision does not affect the stated
contract, proof route, or admission status. The disclosed draft/head-hash difference,
manifest `./` prefixes, and pre-push provenance wording likewise introduce no finding.

## Integrity and the two evidence builds

All checks below were recomputed independently from retrieved Git objects and archive bytes.

| Check | Result |
|---|---|
| Round-2 outer `SHA256SUMS` | **20/20**; `bundle.md` SHA-256 `23a5ad24b674d30a0b378df6373d4e8fd7a093c6d5ee1631cb99542f42e76619` |
| Round-1 outer pack | **10/10**; its `pack.md` equals the round-2 copy |
| Round-2 verification archive | **5/5**, exactly the manifest paths plus `SHA256SUMS` |
| Round-1 verification/nested evidence | **44/44**, **106/106**; exact file sets; all **27** extracted evidence files equal their originals |
| Round-2 intermediate evidence | **118/118**, 119 files including its inner manifest; outer and inner manifests agree |
| Round-2b final-head evidence | **120/120**, 121 files including its inner manifest; outer and inner manifests agree |
| Bundled sources and records | All **14** sections match their specified Git blobs, allowing only the bundle separator newline |
| Source closures | **308/308** Git-blob matches at each head; same paths; exactly the two PR files differ |
| Source metadata | Module: **234 lines**, max width **98**, SHA-256 `c992181ea4cf9e85af6cb1982aa100a5ecd2aabf46e0a8955ba0398e7e0d5356`; facade: **211 lines**, max width **100**, SHA-256 `073bb72d696d715a908fea7aa1ed7600886811a7698b24d672c1b2dd863f8c18` |

The verification archive's decision log is explicitly from `c080a840`, as its provenance
says. The requested records revision adds only the final round-2 pack staging row; that
newer row was also read. It adds no changed ruling. The registry itself matches both pins.

| Recorded build/probe | Intermediate `2f9333b9` | Final `0c04d1eb` |
|---|---|---|
| Module builds | **63/63 rc 0**, 0 errors, 23 warnings | **63/63 rc 0**, 0 errors, 24 warnings |
| Intended admission warnings | Host, declaration line 191 | Host and corollary, declaration lines 192 and 225 |
| Whole-file seal | Five names; passes | Seven names; passes; own-import six-name variant also passes |
| Stronger intermediate seal | Two errors inside the corollary | That proof is removed |
| Paired controls | Two expected failures, unsealed rc 0 | Exactly four expected failures at lines 245, 249, 255, 263; unsealed rc 0 |
| Consumer probe | Only its deliberate control fails, line 56; unsealed rc 0 | Same |
| Lint | Cryptography **92 FAIL / 101 WARN**; Complexity **25 / 391** | Same; independently recomputed FAIL/WARN sets unchanged |

For both builds, all 63 source hashes and log hashes agree with their source revisions and
the archived logs. Diagnostic counts were recomputed for both `error:` and `error(` forms.
The final-head seal probes contain the exact audited module body. The extra ModelInvariance
import is probe-only, needed to name `DecidesInTimeVia`; it is absent from the actual module.
The reader has only the standard three axioms; both admitted statements include `sorryAx`.
The Checks log is unchanged between these builds; its existing canonizer admission is
outside this change. The restored object snapshots are identical, SHA-256
`457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`.

**Execution limit:** Lean and its compiled dependencies are absent from this audit
environment. I did not independently rerun the Lean builds, seals, or axiom prints. The
results above verify their recorded source/log pairs and internal consistency. The supplied
Python verifier does not prove either admitted theorem.

## Changes since round 1 and the moved base

Independent Git comparison confirms two additional commits and exactly two changed paths
since round 1: `SeedMajority.lean` (**97 insertions / 26 deletions**) and the facade's Contents
entry (**2 / 1**). Against the original merge base, the complete PR is **239 additions,
0 deletions**, in those two files. All frozen files are unchanged. With Git's index
abbreviation length set to nine, the independently generated patch equals `pr.diff-r2.txt`
byte for byte; the three-dot diff against `c080a840` is the same patch.

The only non-record changes between the base and staged target tip are #311's new
`SpecialEncryptionMulti.lean` and its `SecureComputation.lean` facade entry. The merge is
clean and independently reproduces tree
`6d24a1fc6be5bd2f4ebbfccb64e66d3de1449a5d`; relative to the tip, only #312's two paths differ,
with exactly the head blobs. The #312 import closure has 308 modules; #311's has 145. Neither
contains the other PR's changed modules, and the three #312 names do not collide with #311.

A combined-tree Lean build has **not** been supplied or run. I do **not** make that a
prerequisite for closing this statement gate: unlike #307 at Gate 24, the moved-base modules
do not import the changed layer, and the only common downstream surface is the unchanged
root facade. The clean merge, unchanged dependency closures, distinct
declarations, and verified per-head evidence suffice here. This is not a claim that the
merged tree has been compiled.

The new findings are G28-R2-01, G28-R2-02, and N28-R2-01. Before dispatch, complete the already recorded brief,
checkpoint, order, and roots update; the later fill owns both pre-approved shared-file
changes and both admitted results. The user retains dispatch and merge control.

## Evidence and reproduction

The companion ZIP contains this Markdown, verification results, Git-blob maps, exact diffs,
bundle/import checks, the captured PR description/metadata, focused source evidence, and
`verify_gate28_r2.py`. Its README gives the byte-check reproduction command using the two
pinned exchange packs. No repository-provided script was executed as audit policy.

**Glossary.** `S` is the displayed majority language; `B(n)=c·2^{w(n)}(n+1)^e` is its machine
budget; `R=2^{w(n)}` is the seed count; `word_w(i)` is the width-`w` binary expansion of rank
`i`; `a_i` is the acceptance tally after `i` tests; `count` is an accepting-seed cardinality;
`T` is a common per-round polynomial
budget (and, in the corollary paragraph, its explicitly specified class bound); `A,c₀,c,e`
are fixed budget constants/degrees. For the envelope, `b=B(|x|)` and `p(v)` is work head
`j`'s position at time `v`. In the consumer route, `m` is the original coin width, `ℓ` the
ceiling-root width, `d` its fixed degree, `n₀` the exception threshold, `s` a PRG seed length,
and `ε>0` the requested subexponential exponent. Other variables retain the meanings in the
audited statements.
