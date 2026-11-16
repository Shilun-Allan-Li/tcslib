# Pass–shelat Gate 34 — sc-ot findings

**Verdict: HOLD.** Severity counts: **0 blockers, 2 majors, 0 minors, 0 notes**.

The proof audit found no mathematical defect in the two targets. The hold is for two further public-lemma duplications whose actual public relatives are absent from the disclosures and DL-48.

| Pin | Audited revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib`, draft [#318](https://github.com/Shilun-Allan-Li/tcslib/pull/318) |
| Lean head | `f62a25b3eda099c9cf9371900664752e7b89007d` |
| PR base | `a334ec2e1d87dbde7eac40812286ba60e85c9078` |
| Campaign records | `5d719839503c1f29f65f5ffa200410349a782276` |
| Exchange | `a74d11833a0814bb686a4b961c5712957008d6a9` |
| Audit date | 2026-11-15 |

## Findings

Paths in the first column are relative to `TCSlib/Cryptography/`.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G34-01 | **major** | `SecureComputation/ObliviousTransfer/Efficiency.lean:198,203` · `OT.getD_zero_eq`, `OT.getD_one_eq'` | Both re-prove specializations of the already imported public `TCSlib.Cryptography.headD_drop`; this public overlap is undisclosed. | `Foundations/BitLists.lean:50–51`; worker report §3; review duplication search item 8; independent import-closure check. | Preserve the headers and derive both proofs from `headD_drop`, then correct the overlap records. No new import is needed. |
| G34-02 | **major** | `SecureComputation/ObliviousTransfer/Simulators.lean:210–212` · `OT.length_ofFn_coins` | This repeats the existing public `Composability.NMSim.length_ofFn_coins`, including its statement and proof. That overlap is undisclosed. | `Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`; exact declaration-code comparison; worker report §3. | Preserve the header and use the existing public theorem with an explicit import, or obtain an explicit disposition for a shared promotion. Correct the overlap records. |

### G34-01: the missing public relative is `headD_drop`

The existing public theorem is

```lean
theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) :
    (l.drop i).headD d = l.getD i d
```

Consequently, the two new statements follow directly from its symmetric instances at `i = 0, 1`. Proposed replacement proof bodies are:

```lean
-- getD_zero_eq
by
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.headD_drop y 0 false).symm

-- getD_one_eq'
(TCSlib.Cryptography.headD_drop y 1 false).symm
```

The delivered proofs instead split the list into cases and finish by reflexivity. `BitLists` is already in `Efficiency`'s transitive import closure, through `Shape`, `Defs`, and `Asymptotic/Adversary`. The public theorem is unchanged since the issue base.

The worker lists these two new names, but identifies only `List.getD_cons_zero` and `List.getD_cons_succ`, explaining that those cover cons lists only. The exact general public relative above is missing. The maintainer's duplication review item 8 likewise misses it. DL-48's F-07 concerns **`OT.getD_one_eq` without the apostrophe**, the encoded-history reader; it does not cover these two list readers. This is therefore outside that disposition and is major under the gate's binding duplication rule.

### G34-02: an identical generic coin-length theorem already exists

Both declarations contain exactly this code, under different namespaces:

```lean
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]
```

The existing namespace is `TCSlib.Cryptography.Composability.NMSim`; the new one is `TCSlib.Cryptography.SecureComputation.OT`. The existing declaration is public and unchanged since the issue base. The independent comparison confirms identical declaration code.

The worker's overlap table groups `OT.length_ofFn_coins` with coin equivalences and cites `Collection.owfCoinsEquiv` / `NUPPT.coinsEquivPoly`, with “specific layouts” as the explanation. This theorem is generic over every `NUPPT`; that row does not disclose its identical public predecessor. DL-48 does not name this overlap. The dependency check finds no import path from `NonMalleability/Simulation/Rounds` back to the OT simulator helper, so importing the existing theorem has no source-level cycle.

The replacement snippets and import proposal above are recommendations; they were not locally compiled or applied.

## Verification and proof assessment

**Integrity and scope.** Independently verified all **18/18** top-level `SHA256SUMS` entries, **112/112** entries inside `verification.zip`, and **810/810** entries inside `review-evidence.zip`. The archives contain exactly their manifests plus `SHA256SUMS`, with no duplicate or extra entries. Every top-level pack file matches the pinned exchange Git object. All **128/128** source-closure files match the pinned Lean head, and the archive equals the independently computed import closure. The seven-file diff matches `pr.diff.txt` byte-for-byte with nine-digit Git index abbreviations. Every changed file lies in the permitted scope.

The 14 supplied records match their declared `1321b9cb` provenance. At the requested campaign pin, 13 remain identical; the plan only appends the Gate 34 registration row. That causes no substantive discrepancy.

**Frozen statements and landing edits.** Independent source comparison confirms **141 added, 0 changed, 0 removed** statement headers: all 52 pre-existing declarations retain their headers and order; every pre-existing definition and every non-target proof retains its code. Only the two target docstrings change, with their statement prose preserved. `EnhancedHardCore` and its docstring are unchanged under G3-8. The supplied frozen checker reports zero differences, with exactly one difference in each of its five controls. LE-doc changes exactly 50 docstrings and no other text; LE-reuse changes only the permitted proof and provenance parenthesis in `Efficiency.lean`.

**Efficiency.** The raw-machine equalities cover empty, singleton, two-message, and longer histories, including empty messages. Polynomial-time composition uses published machine and encoding readers. The message-length argument bounds the index by `Q₁`, samples by `Q₂`, evaluations by `Q₃`, Bob's pair by `3(Q₂ + Q₃) + 2`, and Alice's mask pair by 5. Thus the stated `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` covers the five-message transcript and both empty fillers.

**Alice.** At every generated index, the proof chains statistical closeness bounds

\[
\operatorname{eval}(\operatorname{Sample})
\;\xrightarrow{\delta(n)}\;
\operatorname{encD}(\operatorname{perm}(U))
\;\xrightarrow{0}\;
\operatorname{encD}(U)
\;\xrightarrow{\delta(n)}\;
\operatorname{Sample}.
\]

Here the first step uses `SampleClose`, the middle step uses the permutation bijection, and the last uses canonical decoding. The shared-index product lemma averages a bound valid for each index; the second sample and the branch-dependent coin swap preserve it. Mapping to the full view and applying `distAdv_le_of_statClose` gives **`2δ(n)` for every `n`**, with no eventual threshold.

**Bob.** The masks are correctly read through `inv_runAtL_ones`, `inv_eq_encD`, canonical decoding, and `henc`. `viewDist` retains the challenge's sampler coins inside Bob's tape and retains `D`'s advice. With the pack's acceptance quantities `U₊, U₋`, the verified identities are

\[
P_{\rm real}=U_+,\qquad
P_{\rm ideal}=\frac{U_++U_-}{2},\qquad
\Pr[\mathrm{predict}_{\rm false/true}=B]
=\frac12\pm\frac{U_+-U_-}{2}.
\]

The two hard-core bounds therefore give

\[
\frac{U_+-U_-}{2}\le\varepsilon_{t,0}(n),\quad
-\frac{U_+-U_-}{2}\le\varepsilon_{t,1}(n),\quad
\operatorname{distAdv}_B
=\frac{|U_+-U_-|}{2}
\le |\varepsilon_{t,0}(n)|+|\varepsilon_{t,1}(n)|.
\]

All eight input triples and both signs are instantiated: **16 fixed machines**, whose absolute negligible bounds are summed. This supplies one input-uniform negligible `ε_B`, and the final `2|δ| + ε_B` bounds both sides. The reduction does not require a predictor to know the generated trapdoor. The protocol and Alice simulator agree with [PS10, Protocol 160.4 and Proposition 161.5, pp. 161–162](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf); the source leaves Bob's simulator as an exercise. The declared enhanced hypothesis is preserved as ruled.

**Rule 10 and controls.** All 32 supplied base/head seal probes across strict/coe and A/B have verified probe hashes. Removing their recorded insertions reconstructs the corresponding audited source bytes exactly. The 121 imported non-unit sources are unchanged from the r1 base to the audited head, supporting transfer of the r1 probes. Canonical coe-A passes all seven modules. The canonical controls have 20 probes and 61 sealed negatives, all correct. Strict controls have 71 sealed negatives, each failing once; their only ten discrepancies are `ctlCoeReader`. The raw diagnostic confirms the stated mismatch between a projected `.prob` reader and the sealed `CoeFun.coe` statement. The strict `ctlCoe` negative does fail once. F-09's attribution is correct. The supplied explicit-read scan records 742 items and zero foreign-definition reads.

**Builds, axioms, and documentation.** Verified all 139 reported build-source hashes against the head and all 139 raw log hashes; every return code is zero and neither error form occurs. The 234 census rows have only `propext`, `Classical.choice`, and `Quot.sound`; this includes both targets and `otProtocol_hbcSecure`. The supplied whole-tree result is OK for 1250 modules. New formulas, readers, sketches, sizes, and widths show no further defect; the seven Prop-formula docstrings are acceptable, and `receiverNext_eq`'s long header with an `rfl` proof is a sketch-checker artifact.

This was an independent source and supplied-evidence audit. Lean was not rerun locally. The pending merged-tip integration rebuild remains the maintainer's merge condition, as instructed, and is not a finding.

## Closure requirement

Resolve **G34-01 and G34-02** by reuse, or obtain an explicit user disposition covering these additional overlaps. Then refresh the affected source, disclosure, build, axiom, and seal evidence. Existing DL-48 dispositions remain respected.

## Notation

`n` is the security parameter; `U` is a uniform domain element; `δ(n)` is the sampler's statistical-closeness bound; `D` is the distinguisher. `B` in the predictor identities is the enhanced bit; `P_real, P_ideal` denote real and ideal acceptance probabilities, and `U₊, U₋` denote acceptance with that bit and its complement. `t = (b,a₀,a₁)` comprises Bob's choice bit and Alice's two input bits; `ε_{t,0}, ε_{t,1}` are the two negligible prediction bounds, and `ε_B` is their sum of absolute values over all triples. In the efficiency paragraph, `Q₁, Q₂, Q₃` bound the index, sample, and evaluation lengths, and `B` instead denotes the message-length polynomial, following the pack.
