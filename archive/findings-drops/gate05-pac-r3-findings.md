# Gate 05, round 3: external audit findings

Audited [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194) at `f0385dac9ff477ef2debff7336d454b1a28b8818`, against parent `6b781240bc438a103291c74b2ffefaa910f1a70d`. Date: 2026-11-05.

**CLOSE under the pack's criterion: 0 blockers, 0 majors, 2 minors.** The substantive round 2 repairs are adequate. The confidence-amplification obligation is now expressly assigned to layer 2; the expectation argument and sampling references are corrected. Two qualifications would make the new prose literally accurate. Neither requires changing a Lean declaration or proof.

## Findings

Line numbers below are within the extracted files, not the concatenated bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | **minor** | `TCSlib/LearningTheory/PAC/Defs.lean:196`, `:224` · `WeakLearnsUnder`, `WeakLearns` | The source comparison needs an explicit qualification that the chosen parameters hold uniformly over the indexed class. It substitutes the target-dependent quantities `1/p(n, size(c))` and `1 − 1/q(n, size(c))` into predicates with one fixed `m`, `L`, `γ`, `δ` and a universal target quantifier. The opening sentences also leave “for every `i`” implicit. | `PACLearnsUnder` is `∀ i, 1 − δ ≤ accuracyProb D (C i) m L ε`. Bounds certified for one target do not certify that formula for the whole class. The example below has sufficient sample count for every target but different certified success probabilities. | Add “for every concept `C i`.” State the source comparison on a fixed instance-dimension and target-size slice, or after obtaining common sample, edge and confidence bounds for the entire class and one common learner simulation. A target-specific substitution directly gives only that target's accuracy guarantee. |
| R3-2 | **minor** | `TCSlib/LearningTheory/PAC.lean:26`; `PAC/Prediction.lean:34`, `:204`; `design/S3d-pac-learning.md:49` · amplification prose | “Only after confidence amplification” and “must first be amplified” overstate necessity. Amplification supplies a stronger guarantee when the available guarantee is insufficient; a learner meeting the original weak-learning definition may already have the needed confidence. | The learner returning the observed label as a constant hypothesis learns the two constant concepts exactly from one example. It satisfies the original weak condition and every nonnegative failure parameter without amplification. More generally, the bridge already applies whenever its actual hypotheses are certified for the original learner. | Say: “Starting only from the original weak guarantee, obtain the required confidence by amplification unless it is already certified.” Retain the requirement to account for the learner actually used, including its sample count, running time, edge and prediction bound. |

R3-1 is a missing uniform-instantiation qualification, not another arbitrary-confidence requirement. Fixed-size slices or common bounds repair it. R3-2 is an overstatement of necessity, not a failure of the proposed amplification route. These are nonblocking documentation issues; the bridge itself is correct.

## Required resolution ledger

R2-1: **fixed** — The false attribution of arbitrary confidence to KV94 §4.1 and the same-learner inference are removed. The repair records a changed learner and its resources and edge. The remaining qualifications are separately identified in R3-1 and R3-2.

R2-2: **fixed** — The design note now states `γ + δ < γ' ≤ ½`, explains the accuracy-event/complement split, and records amplification. `resolutions-r2.md` expressly amends the earlier F5/F11 entries; retaining those historical entries is not an unresolved contradiction.

R2-3: **fixed** — `Samples.lean` and its `iid` docstring now cite both SSBD14 §2.3.1 and §3.1, Definition 3.1. The new resolution correctly identifies §3.1 as retained and §2.3.1 as added.

F5: **fixed** — The precise gap condition and the separate source-to-bridge amplification obligation are present in the theorem documentation and design note.

F6: **fixed** — The fixed-distribution and fixed-parameter meanings are disclosed, and the erroneous source convention is corrected. R3-1 requests an additional qualification about the universal target quantifier.

F11: **fixed** — `expect_le_add_of_le_one` correctly requires only an upper bound on the function; the design note now describes an expectation split rather than Markov's inequality.

F14: **fixed** — The current references and the superseding resolution agree with the checked source locations. The earlier inaccurate entry is explicitly amended.

## R3-1: exact counterexample and correction

Take a nonempty Boolean domain and the two constant concepts `C b x = b`. Give the true concept representation `0` and the false concept representation `10`, so their representation lengths are respectively 1 and 2. This example extends to every Boolean dimension with the same two constant concepts.

Use one labelled example and a uniform coin `r ∈ {0,1,2,3}`. If the observed label is true, output the constant true hypothesis for `r = 0,1`, and false otherwise. If the observed label is false, output constant false for `r = 0`, and true otherwise. Thus, under every distribution, the hypothesis has error either 0 or 1, and

| Target | Representation length | Probability of error at most `¼` |
|---|---:|---:|
| `C true` | 1 | `2/4 = 1/2` |
| `C false` | 2 | `1/4` |

The efficient learner meets the target-dependent weak guarantee with

\[
p(n,\operatorname{size}(c))=4,
\qquad q(n,\operatorname{size}(c))=2\operatorname{size}(c).
\]

But inserting the true target's parameters, `γ = ¼`, `δ = ½`, into the class predicate fails:

\[
\operatorname{accuracyProb}\ D\ (C\,\mathrm{false})\ 1\ L\ (\tfrac12-\tfrac14)
=\tfrac14<\tfrac12=1-\delta.
\]

The same class predicate does hold at `γ = ¼`, `δ = ¾`. The issue is uniformity, not insufficient examples; the learner can ignore all examples after the first.

In general, after fixing one common simulation `L` and a sample count sufficient for every target in the class, choose parameters satisfying, for every `i`,

\[
\gamma\le\frac1{p(n,\operatorname{size}(C_i))},
\qquad
1-\delta\le\frac1{q(n,\operatorname{size}(C_i))}.
\]

For each `i`, the certified accuracy event is then contained in the event with error threshold `½ − γ`; its probability is at least `1 − δ`. This proves the class predicate. A fixed target-size slice makes the displayed source parameters common directly. If the source algorithm takes target size as an input, that input must likewise be fixed or otherwise handled by the common simulation.

## Source and statement checks

- **KV94:** Checked [§1.2.1, Definition 1, and §1.2.2](https://www.jeffreyheinz.net/classes/18S/materials/Kearns-Vairani-1994-Introduction-to-Computational-Learning-Thoery-Ch01.pdf), and [§4.1, p. 74; §4.2, pp. 76–77](https://www.scribd.com/document/932325987/An-Introduction-to-Computational-Learning-Theory), using reproductions of the primary text. The weak guarantee is target-dependent. Confidence amplification constructs another algorithm using repeated runs and validation, allowing an additive error loss. Accordingly, recording its own sample count, runtime and edge is appropriate. Ordinary PAC learnability remains distinct from efficient PAC learnability; the finite-domain observation establishes the former.
- **SSBD14:** Checked [§2.3.1, especially p. 18, and §3.1, Definition 3.1, p. 22](https://moodle2.units.it/pluginfile.php/757668/mod_resource/content/1/Shalev-Shwartz%20and%20Ben-David%20-%20Understanding%20Machine%20Learning.pdf). Product sampling and i.i.d. examples occur at the cited locations. The stated parameter range and absence of a proper-output restriction in Definition 3.1 are accurate. No polynomial sample or runtime requirement is attributed to that definition.
- **PS10:** Read and visually inspected the supplied book p. 179 / PDF p. 191. The unchanged independent-uniform completion and two-sided-advantage convention remain disclosed. Nothing in this repair changes the prediction game.
- **Bridge:** With `ε = ½ − γ' ≥ 0`, the accuracy-event split gives the first inequality below. The success identity and absolute-value bound give the rest:

  \[
  \operatorname{expectedErr}\ C\ m\ L\le\tfrac12-\gamma'+\delta,
  \qquad
  \operatorname{predictSuccess}\ C\ m\ L\ge\tfrac12+\gamma'-\delta,
  \]
  \[
  \operatorname{predictAdv}\ C\ m\ L\ge\gamma'-\delta>\gamma.
  \]

  This contradicts the theorem's assumed prediction bound. The repaired numerical conditions and proof description match the Lean statement, including its unrestricted real parameters. The other changed main-result and sampling docstrings also match their statements. No logical regression was identified.

## Evidence and limits

- Read all **10 bundle sections**, including the first-section brief before the material under audit.
- Observed bundle SHA-256: `d91f950f71ea9623fbe924f7eae0f62fdd15051f48e54df75609cbe429d42320`. Supplied PDF SHA-256: `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. These are observed hashes, not comparisons against a separately supplied expected bundle hash.
- Independently fetched the specified GitHub commit. Its parent is the stated round 2 head. The four extracted Lean files' Git blob hashes match its four changed-file hashes, and every supplied repair hunk matches the commit patch.
- Reversed the verified patch locally. Removing Lean comments leaves **byte-identical** text in all four parent/head module pairs: no definition, theorem statement, proof, import or option changed. The modules contain **13 definitions and 38 theorems**, with no explicit `sorry`, `admit`, `sorryAx` or axiom declaration in their executable text.
- Independently checked the mathematics above and the four-coin probabilities with exact rational arithmetic. This is a mathematical and source audit, not a new Lean formalization of the counterexample.
- Lean and Lake are unavailable in this workspace. Elaboration and lint success remain the maintainer's attestations; I did not rerun them or `#print axioms`. This round does not certify layer 2, discharge its amplification/resource obligations, or reopen the previously recorded API deferrals.

**Notation:** In the counterexample, `C b` is the constant concept with value `b`, `L` is the specified learner, `r` its uniform four-valued coin, and `size(c)` the chosen representation length. In the source comparison, `n` is instance dimension and `p,q` are the reciprocal-edge and reciprocal-success polynomials. Other notation follows the audited files.

