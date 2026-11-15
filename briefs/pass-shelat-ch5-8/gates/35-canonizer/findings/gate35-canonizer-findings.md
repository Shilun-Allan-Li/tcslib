# Pass–shelat Gate 35: canonizer audit

**Verdict: CLEAR at the pinned head.** No blockers, majors, or minors found. The maintainer’s integration rebuild remains a pending merge condition, outside this audit.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 0 |

**Audited material.** Draft [PR #319](https://github.com/Shilun-Allan-Li/tcslib/pull/319), Lean head `6421ac1631ef08feed297c810f0839b178d2a2bb`, tree `3e16398e47f1c57b1d26c85ed731650dd094940b`; comparison base `a334ec2e1d87dbde7eac40812286ba60e85c9078`; campaign records `034da63a3408d0112fa45df00abb3de3080246d2`; exchange `8b5e96ad8a796a7f3158ffdaa7a6138f83d7a269`, `outbox/gates/35-canonizer-gate/`. The bundle, review, and repository were checked as evidence rather than accepted as conclusions. No repository or PR changes were made.

**Verification performed.** Independently checked Git objects, archive contents, source bytes, proof logic, generated seal sources, raw diagnostics, controls, census records, and duplication candidates. This environment has no Lean executable: the Lean execution results below are verified supplied runs, not a fresh kernel replay. No merged-tip build is claimed.

**Integrity and scope.**

- All **18/18** entries of the top-level `SHA256SUMS` verify. All 19 top-level files, including the manifest, match their exchange Git blobs.
- `verification.zip`: **124/124** manifest hashes verify; exactly 125 file entries including its manifest. Nested `review-evidence.zip`: **838/838** hashes verify; exactly 839 file entries. Its manifest copy is identical. No duplicate or unsafe archive paths were found.
- All **110/110** source-archive files match Git blobs at the audited Lean head. Independently computed the unit’s import closure: 110 modules. All 14 bundle sections match their declared revision/path pairs, allowing only bundle separator newlines.
- The independently generated base-to-head diff equals `pr.diff.txt` byte for byte with the same Git abbreviation setting: **four paths, +133/−28**. The issue-base and comparison-base blobs agree for all three pre-existing unit files.

The independent checks and their results are included in the accompanying evidence ZIP.

**Frozen statement and proof correctness.**

The target header and the complete `CanonizerExp` definition are unchanged. The delivered proof establishes the frozen existential, with no added hypothesis.

1. `oneTapeMachineFormat.exists_polyCanonizer` supplies a machine `C` and `d : ℕ`, computing
   `α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)` within `d · (n + 1)^d` steps. The two readers give, for every bit string `α`,

   \[
   \begin{aligned}
   &\mathrm{oneTapeMachineFormat.serialize}
     (\mathrm{oneTapeMachineFormat.decode}\,\alpha)\\
   &\quad=\mathrm{oneTapeFormat.serialize}
     (\mathrm{oneTapeFormat.decode}\,\alpha)
     =(\mathrm{codeDecode}\,\alpha).\mathrm{serialize}.
   \end{aligned}
   \]

   Function extensionality gives exactly the helper’s `hf`; `hf ▸ hC` transports the computation contract in the correct direction.

2. The constructed `EffectiveMachineCode` has `encode := CodeTM.serialize`, `decode := codeDecode`, padded decoding law `codeDecode_serialize_pad`, canonizer `C`, and `canonizerTime n := d · (n + 1)^d`. Its required fixed serialization is therefore exactly the function proved in step 1. The time contract is universal over input strings. Failed parses use the prescribed fallback; no validity assumption excludes malformed codes or unusually large encoded state counts.

3. For every `k, d : ℕ`,

   \[
   \begin{aligned}
   k+1&\le 2^k &&(\mathrm{Nat.lt\_two\_pow\_self}),\\
   (k+1)^d&\le(2^k)^d
       =2^{kd}=2^{dk},\\
   d(k+1)^d&\le d\,2^{dk}.
   \end{aligned}
   \]

   In Lean, `k < 2^k` is the required successor inequality. In `hpow`, `rw [mul_comm, pow_mul]` changes the right side to `(2^k)^d`; `Nat.pow_le_pow_left hk d` and then `Nat.mul_le_mul_left d` finish the bound. If `k = 0`, both sides of the final bound equal `d`. If `d = 0`, both equal `0`, including when `k = 0` under Lean’s convention `x^0 = 1`. No division or positivity premise is used.

4. Choosing `A = B = d` proves `CanonizerExp c`. The target’s `⟨c, d, d, h⟩` is consequently correct.

Source: `Universal/Canonizer.lean:50–81`, `Universal.lean:291–308`, `Encoding.lean`’s `MachineCode` and `EffectiveMachineCode`, and `CodeSimulator.lean:8371`.

**The two pre-approved frozen-file readers.**

Both additions exactly match the 2026-11-14 ruling in the pinned campaign records:

| File | Added theorem | Verification |
|---|---|---|
| `CodeFormat.lean:585` | `oneTapeFormat_serialize_decode` | Approved equation, `xs : List Bool`, `rfl`, formula docstring, no attribute; follows `codeDecode_serialize_pad`. |
| `CodeSimulator.lean:193` | `oneTapeMachineFormat_serialize_decode` | Approved equation, `α : List Bool`, `rfl`, formula docstring, no attribute; follows `oneTapeMachineFormat`. |

Deleting precisely the five and seven added lines respectively recovers each base file **byte for byte**. Thus all previous declarations, prose, imports, and attributes in those frozen files remain intact. The other two changed paths are the owned module and its permitted helper. No additional frozen-file exception is used.

**Axiom closure.**

The raw dependency trace reports **8,151** reachable constants. It includes `exists_polyCanonizer`, `computesFunInTime_appendBit`, and both readers; it excludes **both `appendBitTM_computes` and `sorryAx`**. The positive control prints `sorryAx` for the admitted `appendBitTM_computes` itself. The target, the two helpers, and the reused polynomial canonizer print only `propext`, `Classical.choice`, and `Quot.sound`.

The trace traverses `ConstantInfo.getUsedConstantsAsSet` recursively. Checked Lean v4.25.0’s implementation in `Lean/Util/FoldConsts.lean`: it reads types and values, including opaque values, and handles inductives and recursors. Elaborated instance arguments, matchers, and auxiliary proof constants are traversed when referenced; they are not omitted by a source-name filter. The traversal and independent axiom prints support the claimed exclusion.

Independently parsed the stored-constant census: **1,073 → 1,077**, four additions, no removals, no changes to the recorded types or attributes. Its head axiom union is precisely the standard three. The sole changed axiom set is the target’s removal of `sorryAx`. The 1,077 stored constants and the 8,151-constant dependency closure are different counts.

**C-F01 and LE-doc.**

Accept **C-F01 as the recorded LE-width-class disposition**. Outside the authorized module prose, target prose/proof, and added import, the owned file is identical after whitespace normalization. The two header-byte changes are exactly `length_univArg` and private `exists_preimage_of_fUniversal_eq`; two further declaration bodies are re-wrapped. The changes split expressions and tactic sequences without changing tokens or scope. The frozen target and conditional headline statements remain intact. The owned file changes from six over-width lines to zero.

Independently checked `11b24a7e..6421ac16`: **LE-doc changes one helper docstring only**, adding the computation formula. Removing doc comments makes the two helper-file versions byte-identical. This resolves C-F03.

**Rule 10 and C-F02.**

Checked source hashes and every source-to-probe line mapping in **28** generated whole-file probes. The probe bodies preserve their source files. Canonical seals are **coe-A**; B and strict variants are also accounted for.

| Module | Base → head errors | Assessment |
|---|---:|---|
| New `Universal/Canonizer` | — → 0, all four variants | Both helper proofs pass. |
| `Universal`, A / B | 10 → 10 / 12 → 12 | Same failing declarations and per-declaration counts; target adds none. |
| `CodeFormat` | 14 → 16 | Exactly two diagnostics in the new reader; all previous counts unchanged. |
| `CodeSimulator`, full-file rerun | 177 → 177 | Same 58 declarations and per-declaration counts; reader adds none. |

For **C-F02**, independently recounted both full raw logs using both `error:` and `error(…)` forms and mapped all errors back to declarations. Both reach `G06-SEAL-END … requested=1232 verified=1232` and record `lean rc=1`. Their generated sources equal the original coe-A sources plus the documented option line; the full runner passes `-DmaxErrors=0`. All eight base/head, A/B, strict/coe `CodeSimulator` request lists are identical. The truncated 101-error runs are not used to establish full-file equality.

The `CodeFormat` reader’s two errors are the disclosed **C-F06 cascade**: its own `oneTapeFormat` construction already fails under the base seal, leaving its `Code` projection unable to reduce as expected. The new equation unfolds only definitions from its own file. Its direct `rfl` proof and placement satisfy the pre-approved exception; this is not a new foreign-definition read.

Independently checked canonical paired controls: **14 probes, 16 sealed negatives**, each negative failing once, with reader positives passing and no stray errors. Strict controls have **16 probes, 21 negatives**; the only extra positive failures are the two attributed `ctlCoeReader` cases.

In the helper’s seals, each format equation fails by `rfl` and passes through its approved reader. Together with the passing helper proofs this establishes the needed interfaces and their sufficiency. The controls alone do not prove that no alternative public lemma exists; the source searches supply that additional check.

The explicit-unfold scan’s 224 foreign items are all in untouched base declarations. The touched proofs introduce none. The helper does not unfold the owned `CanonizerExp`; its projection reduction is of its own structure literal. No forbidden read was identified.

**Duplication and documentation.**

Independent searches covered the pinned TCSlib sources, Mathlib commit `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, and the relevant Lean v4.25.0 core sources. No undisclosed copied private proof or re-proof of an existing public statement was found.

- `exists_polyCanonizer` is reused, with its specification transported through the readers.
- Repeating the effective fields of `exists_uniformMachineCode` is disclosed and justified: its `Nonempty UniformMachineCode` statement hides the required numerical bound. The other disclosed effective-code existence results do not export this bound.
- `CodeFormat.exists_canonizer` and private `codeCanonical_machine` export an arbitrary length-only time bound. `codeCanonical_eq` has a different left side and supplies neither missing format bridge.
- `expPoly_poly`, `succ_pow_le`, and the private EXPCOM budget proof are related estimates, not the helper’s statement. The inline inequality directly uses the published power lemmas. C-F05 does not warrant a duplication finding.

All four new public theorem docstrings state their formulas with the correct argument order; the source-derived existence claim has its PS10 attribution. The revised target sketch describes the delivered proof. The unchanged `length_univArg` prose explains the recorded pre-existing NO-FORMULA row. The sketch audit finds three qualifying proofs and zero missing sketches. No new definition, abbreviation, instance, or simp attribute is introduced. The owned file and helper have 955 and 83 lines respectively, with no line exceeding 100 characters.

**Build evidence and merge condition.**

Independently verified all **191** recorded head-build source hashes and raw-log hashes, recounted both diagnostic forms, and checked the terminating `done` record: every module has rc 0 and zero errors. The supplied 1,245-module whole-tree check records `RESULT OK`. These are unmerged-head results. The maintainer must still run the integration rebuild specified in the dispatch, including the second merge of #318/#319 as applicable. This audit neither treats that pending work as a finding nor certifies a combined tree.

**Findings:** none. Gate 35 can close at the audited head under the supplied rulings and dispositions.

**Notation:** `C` is the canonizer machine; `c` the constructed effective machine code; `α` an input bit string; `d` its polynomial-bound parameter; `k` an arbitrary code length; `A, B` the exponential-bound witnesses.
