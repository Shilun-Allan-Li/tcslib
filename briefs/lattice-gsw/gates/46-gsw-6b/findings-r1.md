**Gate 46 · GSW phase 6b · round 1**

**PR #376: CLEAR. PR #377: CLEAR. Overall: CLEAR.** There are no blockers or active majors. Two documentation minors remain in #377, plus one already tracked efficiency item. These counts concern the audited heads; historical issues repaired before dispatch are graded separately below.

| PR | Audited head | Blocker | Major | Minor | Note | Verdict |
|---|---|---:|---:|---:|---:|---|
| [#376](https://github.com/Shilun-Allan-Li/tcslib/pull/376) | `04ba2446f541c39dd02aefaa97a9eb31dbbda748` | 0 | 0 | 0 | 0 | **CLEAR** |
| [#377](https://github.com/Shilun-Allan-Li/tcslib/pull/377) | `7563734a8badba842223e0687c719b3b4692e9d2` | 0 | 0 | 2 | 1 | **CLEAR** |
| Overall | Both pinned heads | 0 | 0 | 2 | 1 | **CLEAR** |

Exchange pin: `8cfb07b12373974d324fb99f47fc2e035dce6aef`. Campaign-records pin: `1404eff9d9d9f55f7e4687a87395dec70dbb791e`. The review uses the issued source versions, plan r3 and the recorded rulings. The 6a proofs, #368, and U12–U19 fills are outside scope. No PR, branch, comment or merge was changed.

| Finding | Severity | PR · location | Evidence and proposed fix |
|---|---|---|---|
| **G46-01** | **minor** | #377 · `GSW/Circular.lean:101`, `WeakCircularSecure` docstring | The explanation that quantifying over every function forces epsilon near one lacks a correctness qualification. Counterexample: `n=0`, `q=2`, `ℓ=N=1`, uniform Boolean noise and `m` samples. The largest advantage between the complete FHE views is exactly `2^(−m)`, even for unbounded tests. These parameters are permitted by the definition but fail correctness separation. Qualify the explanation to correctly decrypting parameter regimes; say an unbounded test can enumerate a compatible key-generation seed and decrypt. Recovering the original secret uniquely is unnecessary. The predicate and reader are correct. |
| **G46-02** | **minor** | #377 · `GSW/Asymptotic.lean:77`, `encodeCiphertext` docstring | `[Pei16, Def 4.2.3, p024-b001]` defines decision-LWE; it does not specify the claimed binary representation convention or the ciphertext encoding. The implementation is sound technical glue. Remove this attribution, or identify the encoding as a local choice and cite §5.4.3, `p052-b001`, for canonical binary residue expansion. This is a technical-glue citation defect, not a fabricated theorem or a changed security claim. |
| **G46-03** | **note · known** | #377 · `GSW/Asymptotic.lean`, A4 and honest algorithms | The domination hypotheses do not prove machine reductions or honest-algorithm efficiency. This is the single known rule-15 item expressly retained by the gate ruling. The hypotheses cover the exact reductions, are satisfiable and insert no extra security assumption. Preserve the recorded condition that #377 does not merge until the lattice-wide remediation plan exists. |

**Verification.** All 18 outer checksums pass. `bundle.md` has SHA-256 `1c9c53cdbefbd9bc1b8c1bd042961b9b96b1eb7cbd3feebbc09d930e3ab1e2da`; all 49 sections match their referenced contents. The manifests verify **46/46** entries in `verification.zip`, **25/25** in phase 1, **598/598** in phase 2 and **224/224** in LE-g46. All 59 Git-origin source entries match their declared Git blobs. The five packaged Mathlib/core files also match independently retrieved upstream blob IDs.

The records copy of `pack.md` differs only by the expected substitution of its `<RECORDS>` self-pin; its manifest correspondingly omits the exchange-only wrapper files. This is not source or evidence drift.

#376 is insertions only: one path, +58/−0, declarations **5/0/0**. #377 adds nine files and changes the two permitted facades. Together they touch exactly the brief's **12 paths**; no frozen 6a or phase-5 file changes. The new `NeZero P.columns` instance follows from existing parameter fields and weakens no frozen statement.

Applying LE-6b1, LE-6b2 and LE-6b3 in order reproduces all five landing files byte for byte. Their only non-comment change is the instance proof's use of `Nat.one_lt_two_pow_iff`. LE-g46 changes code only in the two length-reader proofs; its other three edited files are comment-strip identical. Both readers now use `length_flatten_map_const`; the inline flatten-length derivations are gone.

**O2.** The proof establishes the interval reader for every `q≥2`. Writing `h=floor(q/2)` and taking `0≤v<q`, the strict distance comparison is equivalent to

\[
h<2v<q+h
\iff \lfloor h/2\rfloor+1\le v<\lfloor(q+h+1)/2\rfloor.
\]

Also `decodeLo≤h<decodeHi≤q`. The `hsub` split and `hcast` side conditions are valid, and both distances use the upstream minimal-lift lemma. Supplementary exhaustive evaluation checked **2,000,999** representatives for `2≤q≤2000`, with zero mismatches. The accompanying evidence gives the general argument; this finite check is supplementary.

**Statement fidelity.** All 24 admitted targets pass against the frozen interfaces, issued source passages and ruled deviations. Their hypotheses are usable and compatible; the bounds support the designated fills.

| Target | Assessment |
|---|---|
| G1 `Encrypts.select` | Fresh selector on the left; additive noise `βV+2Nβ`. |
| G2 `encrypts_homEvalPBP` | Permutation pull steps; length times `2Nβ`; zero-length case correct. |
| G3 `encrypts_homEvalFormula` | Barrington length `4^depth`; accepting coordinate `sigma1 0`. |
| G5 `vecMul_secretVector_eq_sum` | Exact gadget identity and dot-product reassociation. |
| G6 `decryptFormula_eval` | Total decryption, O2 and F9 agree for every ciphertext. |
| G7 `nandFormula_eval` | NAND of both decryptions using one key block. |
| G8 `depth_nandFormula_le` | Depth at most `decDepth+1`. |
| G8 `maxFanin_nandFormula_le` | Fan-in at most two. |
| G8 `decDepth_le` | Valid weakening of F10, replacing `ceil(log₂q)` by `ℓ`; admitted as ruled. |
| G9 `encrypts_bootNAND` | Correct key-switching statement; no input-noise hypothesis needed. |
| G10 `decrypt_fheEval` | Every depth; zero-, one- and two-argument NAND padding correct. |
| G18 `decrypt_fheEvalCircuit` | Correct composition with the frozen NAND conversion. |
| G12 `decrypt_keygen_fheEvalCircuit` | Honest-key bound; bootstrapped separation implies input separation. |
| G13 `bootNoise_le` | Constants and exponents `4^33`, `N^19` and fourth power verified. |
| G15 `distAdv_fheView_noEvk_le` | Genuine transport through unused-coin marginalization. |
| L2 `encrypts_leveledEval` | Consecutive keys; output secret at output depth; maximum noise bound. |
| L3 `decrypt_keygen_leveledEvalCircuit` | Literals, exact layering depth and public output level agree. |
| L4 `distAdv_levelHybrid_le` | Top-down planting is valid; random key-bit messages stay inside reduction coins. |
| L5 `distAdv_leveledView_le` | Two challenge-dependent chains plus the exact final challenge term. |
| G16 `bootRatio_le_poly` | Family bounds dominate the explicit polynomial with constant `2^70`. |
| G17 `decrypt_fheEval_of_ratio` | Factor eight implies the strict floor separation, including zero noise. |
| G17 `decrypt_leveledEval_of_ratio` | Same implication plus L3; input separation follows. |
| A1 `indCPA_of_dlweAssumption` | Unchanged DLWE assumption, A4 and width bound suffice. |
| A3 `leveledINDCPA_of_dlweAssumption` | Polynomial hybrid count; A4 includes every level and challenge reduction. |

G11 and L1 are correct proved citations of the phase-5 encryption bounds. G14 and A2 are precisely the two ruled predicate readers. Every public definition has its required reader; no definition depends on an admitted target at the audited head. The evaluation definitions are computable; only the two real-valued advantage terms are explicitly noncomputable.

The noise calculation gives

\[
\operatorname{bootNoise}(\beta)
\le4^{33}N^{19}(\ell+\lceil\log_2N\rceil+3)^4(2\beta),
\qquad8\cdot4^{33}\cdot2=2^{70}.
\]

For `y=ℓ·bootNoise`, `8y<q` gives `2y<floor(q/2)`: if `y=0`, use `q≥2`; otherwise `q≥8y+1≥4y+2`. Factor four alone fails at `q=4y+1`. W1–W3, F1–F2, Q-6B-1 and Q-C1 are implemented correctly. L3's extra input-separation hypothesis is redundant and compatible. Zero noise, zero samples, level zero, empty gate lists and the permitted zero-input cases cause no additional defect; `N=0` is excluded by the parameter fields.

**Sources and duplication.** All **140 anchor occurrences**, representing **36 distinct cited passages**, resolve. Semantic review found the technical citation defect G46-02; the substantive target correspondences and disclosed deviations are supported. BV11 Lemma 4.5 is correctly distinguished from BV14's reference to “Lemma 4.1.”

The Gen09 chain, reverse indices, layering and Theorems 4.2.1/4.2.3 support the new module citations. Gentry's index `i` maps to local `L−i`; his Game `k` corresponds to the *replacement order* of `H_{L−k}`. The docstring explicitly discloses zero plaintexts instead of unrelated-key bits, positional hybrids, direct DLWE reductions and the two-chain challenge step. With those deviations, it does not claim identical game distributions. The declaration-level pointers to this precise module disclosure are adequate. The additional LE-6b2 citations support the named sub-facts, and the sketches use the public readers and shared hosts H18/H19.

I agree with sweep dispositions N1–N11. Name, statement-shape and inline-proof review found no additional undisclosed or unaccepted duplicate. S1 and the instance re-derivation are repaired; G11/L1 are disclosed proved citations, G15 is a distribution transport, and `decDepth_le` is the expressly ruled weakening. The pre-existing flatten-length family is outside this change.

**Execution evidence.** I independently recounted and checked the recorded executions; I did **not** run a new Lean replay.

| Evidence | Independent result |
|---|---|
| Build records | R1: 19 modules; R2: 14; R2-g46: 8. All rc 0; all 41 source hashes and log hashes match the appropriate pinned stage. |
| Admissions | **192 → 192 → 216**; exactly the 24 source targets added, none removed. LE-g46 preserves the complete R2 inventory. |
| Axioms | R2: **175 = 153 DECL + 22 AUX**. LE-g46: **174 = 153 + 21**. `sorryAx` appears in exactly the same 24 targets; no other nonstandard axiom. |
| Seals | All **48** strict/coercion A/B owner probes have zero errors and matching requested/verified sets, including all chunks. |
| Paired controls | Strict and coercion forms each have **70 sealed negatives**, each failing once; positives and unsealed controls pass. |
| Delivered controls | **34** pass unchanged; the remaining **16** pass after exactly the four disclosed names are removed and request counts adjusted. No control example changes. |
| Unfold scan | **101** items; **0** foreign unfolds. |
| LE-g46 recheck | Source-bound rebuild, unchanged admissions, unchanged length-reader axioms and four passing coercion-A owner seals are sufficient. The recorded comparison's `FAIL` concerns only the expected removed compiler auxiliary, not its request sets. |

The request-set changes are the disclosed closure drift: seventeen additions and four vanished `IterateFind` auxiliaries. The absence of a fresh root coercion-A seal is sufficient here: the root is unchanged and owns no declarations, while both changed facades and all owners were sealed. The export, state and object-map records consistently bind the three stages to the audited trees.

| Prior item | Auditor grade and disposition |
|---|---|
| G6B-F01 | **Minor, closed** by LE-6b1; prerequisites are present and proved at this base. |
| G6B-F02 | **Minor, closed**; the settled constant is exactly `2^70`. |
| G6B-F03 | **Minor, closed** by the ruled disclosure of the additional sub-fact citations. |
| G6B-F04 | **Major historically, closed** by LE-6b3. The original inline re-derivation meets the strict duplication standard. |
| G6B-F05 | **Note; agree.** A disclosed, expressly ruled weakening; retain as an admitted target. |
| G6B-F06 | **Note; agree.** Partial probes are disclosed and do not establish the general statements. |
| G6B-F07 | **Note; agree.** Size estimate exceeded; no present size violation. |
| G6B-F08 | **Note; agree.** Disclosed worker-process/provenance issues; no demonstrated source defect. |
| G6B-F09 | **Note, resolved.** The public reader is `hybridPlant_eq`; sketches use it. |
| G6B-F10 | **Note; agree.** Axiom changes exactly match the instance repair and proved prerequisites. |
| G6B-F11 | **Note; agree.** Pruning is confined to the four vanished names; fresh controls cover current sets. |
| G6B-F12 | **Note; agree.** A root seal adds no necessary coverage in this scope. |
| S1 | **Major historically, closed** by LE-g46; DL-61 repayment and direct use of the shared lemma verified. |

The two current documentation minors were not identified in the supplied reviews. I found no further undisclosed defect. **CLEAR is the statement-audit verdict; the recorded rule-15 remediation-plan condition for merging #377 remains in force.** Dispatch and merging remain with the user.

**Notation.** `q`: modulus; `n`: secret dimension; `m`: sample count; `ℓ`: gadget width; `N=(n+1)ℓ`: column count; `β,βV`: noise bounds; `h=floor(q/2)`; `v`: canonical residue representative; `y=ℓ·bootNoise`; `L`: level count; `i,k`: source indices in the Gen09 correspondence; `H_h`: delivered level hybrid. Other names are the audited Lean identifiers.
