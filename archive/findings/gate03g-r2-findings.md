# Gate 03g, round 2 findings

**0 blockers, 0 majors, 1 minor.** The original attempt-count and ideal-coin bridge defects are repaired. `col_zk` remains provable as stated in its declared D8 scope. A worker can follow the revised argument after the branch-local correction in R2-1 below; neither its final error function nor its Lean statement needs changing. The gate meets its stated numerical closing criterion, with R2-1 to carry into the fill. This is a delta statement/sketch audit, not a completed Lean proof or an independent elaboration replay.

Audited Lean pin: `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; round 1 comparison: `0c348ff94cacf24d96d99078c9dd9e328530c8d2`. The supplied bundle has 20 sections and SHA-256 `1ffe0fa50da9c9bdf29c85de14b6393e8038d158b077392f4a273e5fd2ca3489`. The attached source has SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. I read book pp. 124–129 (PDF pp. 136–141) and visually checked pp. 128–129. The extracted round 1 findings, with the bundle separator removed, match the resolutions' SHA-256 `09f349307f40468c95945b2beb41a648e6d95e5bb32c126ffdc36115a5f7f1f2`.

Locations below are file-relative. `ThreeColoring/` abbreviates `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/`. The first pack's brief governed this audit; the review, resolutions, code and execution claims were evidence under audit.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | minor | `ThreeColoring/Simulator.lean:755–771` · `col_zk` sketch; reproduced in review §2.3 | The final aggregation incorrectly applies `K ε_B(n)` to both branches, although `K = nm = 0` in the edgeless branch. That branch has one multi-value hiding gap, bounded by `ε_B(n)`, not zero. | Take an edgeless two-vertex graph and the constant-zero colouring: `n=2`, `N=4`, `m=K=0`. A commitment may reveal its value at security parameter 2 while retaining asymptotic hiding. For this commitment, the test “the first commitment is not the encoding of colour zero” has advantage `2/3` after idealizing the honest permutation, and `85/128` for the actual four-trial sampler; the simulator always commits to zero. Thus the hiding contribution need not be `≤ K ε_B(2)=0`. The calculation and preservation of the commitment hypotheses are given below. | Restrict `K ε_B(n)` to `m>0`; state `ε_B(n) ≤ N² ε_B(n)` separately for `m=0, n≥1`. Equivalently use `max(1,K) ε_B(n) ≤ N² ε_B(n)` for `n≥1`. Synchronize the review/fill guidance. This is minor because the branch's hiding argument is already present and the final `ε` already covers it. |
| R2-2 | note | `ThreeColoring/Simulator.lean:730–777` · `col_zk` | With R2-1 corrected, the revised reduction and all four error terms support the existing statement. | Fixed auxiliary coins give an inequality, not an impossible fair-bit realization of the ideal table. The remaining random tape is exactly `D`'s at parameter `n²`. The maximum is over fixed-reduction gaps, auxiliary input is polynomially bounded, and the empty input is treated separately. Details below. | Complete the scheduled intermediate lemmas and proof; no new hypothesis or stronger simulator is needed. |
| R2-3 | note | `ThreeColoring/{Language,Protocol,Simulator}.lean`; batch evidence | No unreported declaration or semantic change was found in the audited Lean files. The three admissions remain. | Direct comparisons at both pins agree with the supplied repair diff. `Language` and `Simulator` differ only in comments. `Protocol` has one docstring change and two proof adaptations through `Protocol.proverBounded_iff`; its statements and definitions are unchanged. The supplied logs support the reported execution results, subject to the limits stated below. | None for this delta; retain the distinction between statement approval and filling the admissions. |

**Resolution dispositions**

- **#1, #2, M1: not resolved** — the original two major defects and the zero-length issue are fixed, but the resolution's claim of a fully corrected replacement sketch retains the minor all-branches multiplier error R2-1. No major remains.
- **#3: fixed** — `Simulator.lean:681–684` now takes `K = max(n₀,4^c,1)` and `N ≥ K²`, matching the proof. Then `⌊√N⌋ ≥ K` and the printed power comparison follows.
- **#4: fixed** — `Language.lean:303–307` states `m < 2^(Nat.size m) ≤ 2m` only for `m>0` and explicitly identifies the zero-edge default. Powers of two now satisfy the upper equality.
- **#5: fixed** — the simulator module docstring, `colSim`, `col_zk`'s deviation paragraph and the inventory reading guide now attribute the `n|E|` cutoff to Algorithm 128.7 itself. The attached source's steps 4–5 confirm this. GI's separate truncation deviation is retained.
- **#6: fixed** — DESIGN's D8 erratum and §5 item 11 distinguish computational 3COL ZK from statistical GI ZK; the §2.15 as-built note supplies the message-bound completeness clause and `boundedP`. The inventory's Thm-124.1(A), Def-124.a and Claim-124.d include `hLR`, exact polynomial output length, the nonshrinking parameter and the separation of single-iteration ZK from repeated soundness under DQ5. The superseded frozen text is explicitly marked as such.
- **M2: fixed** — `Simulator.lean:321–324` now quotes `S'` with the explicit correction to `S''`. DESIGN §7 item 46 records both occurrences of the source's typo. Both are visible on book p. 129.
- **M3: scheduled** — the seven-step ladder and the sweep of 20 pre-existing lint findings are present in `briefs/pass-shelat-ch5-8/fills/3col/brief-notes.md`. This file is outside the bundle; I retrieved it separately from the campaign branch, blob `1d88b1e4d083ccc5300433e3cb9d8dfb1a52c549`. It schedules the work after gate closure; it does not claim the lemmas are already proved. Carry R2-1 into its assembly step.
- **M4: recorded** — moving `Negligible.comp_sqrt` remains optional, and the retrieved fill notes preserve that disposition. No move is claimed or required for this gate.

**Recomputed bound and adversarial checks**

For a valid instance, let `n` be its vertex count, `m` its ordered-edge count, `N=n²` its encoded length and `K=nm`. Write `Δ` for the distinguishing advantage between the real and simulated encoded views, for fixed `V'`, `Lz`, `D`, instance and witness. From `multiHiding`, `ε_B(n)≥0`: specialize its conclusion to identical message vectors, which exist at every `n`, including zero.

1. **Positive edge count.** The real-permutation replacement costs `4^{-N}`. Each simulation attempt's edge and colour-pair replacements cost at most `2^{-N}+4^{-N}`; independence of the disjoint blocks and product closeness give `K(2^{-N}+4^{-N})`. The pair/permutation bijection costs zero. The attempt hybrid and fixed-coin reduction give a hiding term at most `K ε_B(n)`. The final full-colouring hybrid costs `(1-1/m)^K ≤ e^{-n}`. Hence

   $$
   \Delta\le 4^{-N}+K(2^{-N}+4^{-N})+K\varepsilon_B(n)+(1-1/m)^{nm}.
   $$

   Because `m≤n²` and `n≥1`,

   $$K=nm\le n^3\le n^4=N^2.$$

   Thus the claimed common bound follows:

   $$
   \Delta\le\varepsilon(N):=
   N^2\varepsilon_B(\lfloor\sqrt N\rfloor)
   +e^{-\lfloor\sqrt N\rfloor}
   +N^2(2^{-N}+4^{-N})+4^{-N}.
   $$

   The old adversarial family still tests the repaired coefficient: for the complete tripartite graph with three parts of size `t≥1`, `n=3t`, `m=6t²`, `N=9t²` and `K=18t³`. Although `K/N=2t` is unbounded, `K/N²=2/(9t)≤1`. The new coefficient passes this test.

2. **No edges, at least one vertex.** There is one simulator attempt, even though `colIterations x=K=0`. Since `N≥1`, its allocated tape contains a complete first block. Its commitment coins and verifier tape have the same independent uniform laws as the real experiment. The only difference after idealizing the honest permutation is the committed vector. Fix the permutation, average out the verifier tape with `exists_fixCoins`, and apply the common worst-reduction machine. Averaging over the permutation gives

   $$
   \Delta\le 4^{-N}+\varepsilon_B(n)
   \le 4^{-N}+N^2\varepsilon_B(n)
   \le\varepsilon(N).
   $$

   This is the missing branch-specific aggregation. No edge-sampler or colour-pair error is needed here: their outputs are unused in this branch.

3. **Concrete counterexample to the zero multiplier.** Starting with any commitment satisfying the theorem's hypotheses, change its evaluation on a well-formed pair `⟨v,r⟩` with `|v|=2` to output `v`, and leave other value lengths unchanged. This remains polynomial-time. Binding at length 2 follows from equality of the revealed values; binding at other lengths is inherited. Hiding is inherited except at one length: replacing any negligible hiding bound by its absolute value plus the indicator of `n=2` bounds every distinguisher and is still negligible. Therefore the modified scheme satisfies the same commitment hypotheses.

   On the edgeless graph with `n=2` and constant-zero witness, `padColor 2` distinguishes all three colours. The test in R2-1 is polynomial-time. In the ideal real view its acceptance probability is `2/3`, versus zero in the simulator. In the actual real view, the four three-bit rejection trials all fail with probability `(2/8)^4=1/256`; failure selects the identity permutation and is rejected by this test. Conditional on success the permutation is uniform, so

   $$
   \Pr[\text{accept real}]
   =\left(1-\frac1{256}\right)\frac23
   =\frac{255\cdot2}{256\cdot3}
   =\frac{85}{128},\qquad
   \Pr[\text{accept simulation}]=0.
   $$

   This refutes only the printed zero multiplier. It does not refute `col_zk` or the proposed final `ε`.

4. **Zero vertices.** `N=0`, and the simulator allocates no blocks. A verifier with one coin bit and a distinguisher testing whether the encoded verifier tape is empty give advantage 1: the real tape has length one, the simulated tape length zero. The revised separate case correctly uses `Δ≤1`. The displayed error has `ε(0)=2`, so it covers this discrepancy. No exact-law assertion at zero is needed.

5. **Negligibility.** `ε_B ∘ Nat.sqrt` is negligible by the corrected `Negligible.comp_sqrt`; multiplication by `N²` preserves negligibility. The exponential term uses `negligible_exp_neg_sqrt_div` with constant 1. Both geometric terms are negligible, with `4^{-N}≤2^{-N}`; polynomial multiplication and finite addition finish the bound. Non-square lengths cause no difficulty for this negligibility argument, while `R3COL x y` ensures `N=n²` whenever the security assertion is applied.

**The fixed-coin machine bridge**

I checked `CommitmentLemmas.exists_fixCoins`, `Commitment.multiHiding`, the parameter/advice closure interfaces, `Strategy.Efficient`, view encoding and `ZK` directly at the audited pin. In `colSimRed`, the auxiliary coin factor is the entire ideal attempt table; the remaining factor is `D`'s fair-bit tape. For each fixed table, let `g(w)` denote the difference of its two acceptance probabilities, already averaged over challenge and distinguisher coins. Then

$$
\operatorname{distAdv}(X,Y,\texttt{colSimRed})
=\left|\mathbb E_w g(w)\right|
\le\mathbb E_w|g(w)|
\le\max_w|g(w)|.
$$

The table type is finite and nonempty in the `m>0` branch. The cited lemma therefore supplies a single `w₀` without loss. With that table fixed, the first successes before and after the planted index are constant optional views `pre` and `post`. The reduction is exactly `D'(pre <|> planted(cv) <|> post)`. The planted attempt splices the two fixed endpoint commitments into `cv`, calls the uniform verifier machine on that commitment vector with its fixed tape, tests the decoded edge, and uses the fixed opening if successful. This takes at most one verifier call and one call to `D`; in the edgeless branch no verifier call is necessary. There is no remaining uniform sampling over edges or permutations inside this hiding machine.

Polynomial advice is sufficient, including encoding overhead. If `|Com(u)|≤C(|u|+1)^d`, each endpoint commitment has length at most `C(2n+ℓ(n)+3)^d`, and every commitment vector and opening satisfy

$$
|cv|\le n\bigl(2C(2n+\ell(n)+3)^d+2\bigr),\qquad
|opn|\le3\ell(n)+20.
$$

The literal pairing definitions then give

$$
|\text{encoded view}|
\le4n^2+2L_z(n^2)+2\,V'.\mathrm{coinLen}(n^2)
  +2|cv|+2|opn|+12.
$$

These bounds also cover partial-colouring views; they do not require those colourings to satisfy `R3COL`. The fixed tapes, edge index, endpoint data, `pre`, `post`, `x`, `z` and `D.advice(n²)` consequently have polynomial total length. A fixed number of pair encodings preserves that bound. The evaluator is polynomial-time on arbitrary challenge strings as required by the machine interface, using bounded message extraction/splicing and the verifier's uniform evaluator.

At each vertex count, graphs, colourings, bounded auxiliary strings, indices and coin tables form a finite set. Choose data maximizing the **fixed reduction's absolute gap on its own two vectors**. This makes one advised machine dominate every reduction at that vertex count; maximizing an unnormalized whole-instance hybrid gap instead would need a different explanation of the attempt multiplier. Nonempty edgeless data supply a choice for `n≥1`; arbitrary default advice suffices at `n=0`.

Reparameterizing `D` by `n↦n²` gives `B.coinLen(n)=D.coinLen(n²)`. The remaining coin transport is therefore a genuine bijection of equal-length bit tapes. Applying `hC.multiHiding var B` bounds the selected gap, and hence all fixed-reduction gaps, by one negligible `ε_B`. The simulator was chosen before `Lz` and `D`; only this hiding reduction and its bound depend on them. The required quantifier order is preserved. The missing colour-pair sampling lemma, two-parameter coin transport glue and reduction-machine construction remain fill work, explicitly scheduled by M3; none requires a stronger hypothesis.

**Delta and evidence limits**

The three bundled Lean files match the corresponding GitHub files at the audit pin, ignoring only bundle separator newlines. Against the round 1 pin, removing comments leaves `Simulator.lean` and `Language.lean` identical. In `Protocol.lean`, the only executable differences are introduction/elimination through `Protocol.proverBounded_iff` in `colProtocol_proverBounded` and `col_efficientProverProofErr`. Its changed `colProtocolRep` docstring correctly allows the last verifier message to be the verdict; inspecting `colVerifierRep` confirms that behavior. No definition, signature, import or admission changed in these three files. The batch-wide statement report's ten additions and two changes are outside these files; its two changed declarations are the explicitly identified `NP.lean` wrappers.

I counted 129 distinct successful replay entries, all with zero errors, and eight successful maintainer re-checks. The replay contains 83 sorry warnings across its entire downstream scope; locally these three files still contain exactly three admissions. The axiom output contains 548 distinct declaration results, including 100 with `sorryAx` across the whole batch. Its header explains the “549 prints” figure as 549 requested print commands for 548 names. The six 3COL declarations carrying `sorryAx` are unchanged: `R3COL_witnessRelation`, `colRep_efficientProverProof`, `colRep_interactiveProof`, `col_zk`, `col_hvzk`, and `col_zeroKnowledgeProof`. The base-comparison report records no changed axiom set. The seal report includes a passing current `Protocol.lean`, a failing sealed base control, and a passing unsealed control. Lint records no new warning/failure. These are reconciled supplied execution claims, not executions I independently performed; the complete base axiom output is not supplied for an independent set-by-set comparison.

The additional contextual sources were `CommitmentLemmas.lean`, `Commitment.lean`, `Defs.lean`, `Interaction.lean`, `Randomized/Closure.lean` and `Randomized/NonUniform.lean` at [the audited commit](https://github.com/Shilun-Allan-Li/tcslib/tree/1ea782b11617e15a51c3e2f6bd15dd0e3befbd95/TCSlib), plus the separately identified [fill notes](https://github.com/Shilun-Allan-Li/tcslib/blob/cryptography/pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/fills/3col/brief-notes.md). This audit does not upgrade the three admissions to proofs or claim sequential ZK composition, statistical 3COL ZK, or security for unrestricted auxiliary-input lengths.

**Notation.** `n`: vertices; `m`: ordered edges; `N=n²`: encoded length; `K=nm`: attempt count for the positive-edge branch; `t`: tripartite part size; `Δ`: real/simulated distinguishing advantage; `ε_B`: multi-value hiding bound for reduction `B`; `ε`: assembled error. `V'`: malicious verifier; `D`: distinguisher; `D'`: its encoded-optional-view version; `B`: advised hiding reduction; `Lz` or `L_z`: auxiliary-input length polynomial; `ℓ`: commitment coin-length polynomial. `X,Y`: the two challenge-vector distributions; `w,w₀`: ideal attempt table and its fixed choice; `g(w)`: signed acceptance gap at that table; `pre,post`: constant optional views around the planted attempt; `cv,opn`: commitment-vector and opening strings; `C,d`: constants bounding commitment output length; `u,v,r`: input word, committed value and commitment coins; `n₀,c`: the threshold and requested inverse-power exponent in `comp_sqrt`. Angle brackets denote the existing string-pair encoding; `<|>` selects the first nonempty optional view; `|·|` denotes string length or absolute value according to its argument.
