# Gate 11 findings — probability readers and Regev statistical proofs

| Scope | Verdict | Blockers | Majors | Minors | Continuing notes |
|---|---|---:|---:|---:|---:|
| A · two shared readers, PR #255 | **PASS** | 0 | 0 | 0 | 2 |
| B · six Regev statistical-hybrid fills, PR #250 | **PASS** | 0 | 0 | 0 | 4 |

## Pins and packet integrity

| Item | Audited identity |
|---|---|
| Exchange `exchange/pass-shelat-ch5-8` | `a05328c428875cf9798b57513da9f1e90335cd64` |
| Central target `cryptography/lwe-sis-constructions` | `27f9ea89b72d84abaec8128f2abd826f24aaced4` |
| #255 source / records | `004bd5b89e48dec52e045bba32439375b82eaead` / `6d9d46b5800e3cde7e89eee6b9d712db3c8982fd` |
| #250 statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Prior #250 intake / integrated proof baseline | `bb9ab16e363330f2e0384d128f5d208ca6d760bb` / `22f4d3c2e6ab01ad85698eed156d3728fc259362` |
| #250 Lean/root / bundled records | `f49ea765eb22ea49c0be978e26741e3b721bb162` / `54c569ae08f723f6caa2bbdb7828a80ada90b16d` |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

The bundle is **4,780,683 bytes** with SHA-256 `0c67ef0f22778a23b237074aca9641be71d5ce431bc7c3f571bb65ad59ae6456`. All five gate checksums pass. The two ordered indexes agree on all **214** revision/path, length and digest rows. I matched each extracted section to its Git blob and verified the 15 nested checksums for the statistical fill evidence. Both PRs are open drafts at the specified target. The live #255 head matches the reader records pin. The live #250 head `a6275060297165ddba7c5d67d42f404d29e473db` adds only the two publication records to the bundled records pin. [Gate packet](https://github.com/Shilun-Allan-Li/tcslib/tree/a05328c428875cf9798b57513da9f1e90335cd64/lwe-sis-constructions/outbox/gates/11-regev-statistical-proofs-r1) · [PR #255](https://github.com/Shilun-Allan-Li/tcslib/pull/255) · [PR #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250)

## A · Shared probability readers

- `TCSlib.InformationTheory.isUniversal_iff` exposes the full collision-count predicate. For every distinct input pair the number of colliding seeds, cast to the reals, is at most the seed count divided by the output count. The type needs finiteness of the seed and output spaces and decidable output equality. `omit [Fintype α] in` removes the unused input instance. [UniversalHashing.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/004bd5b89e48dec52e045bba32439375b82eaead/TCSlib/InformationTheory/UniversalHashing.lean#L46)
- `TCSlib.InformationTheory.FinDist.hasMinEntropy_iff` exposes the full pointwise predicate `∀ a, p a ≤ (2 : ℝ) ^ (-k)` for the same distribution and real entropy threshold. Both formulas are definitional `Iff.rfl` readings and leave the simp set untouched. [FinDist.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/004bd5b89e48dec52e045bba32439375b82eaead/TCSlib/InformationTheory/FinDist.lean#L139)

Applying the approved patch to the central blobs reproduces the initial owner source `c744076da5fbb6ea5e14ce7095eeaec33554c124`. The correction adds exactly the `omit` line. The final library diff adds 13 lines across the two owner modules and preserves existing definitions, signatures, imports, exports and pins. I verified all nine framed logs, including the four clean module checks and the three standard-axiom prints for the readers and `leftover_hash`. My fresh serial run of `FinDist`, `StatisticalDistance`, `UniversalHashing` and `LeftoverHash` passed without diagnostics and reproduced the probe byte for byte. Both style runs also reproduced byte for byte. The only removed diagnostic was the missing `HasMinEntropy` reader warning. [Owner evidence](https://github.com/Shilun-Allan-Li/tcslib/tree/6d9d46b5800e3cde7e89eee6b9d712db3c8982fd/briefs/lwe-sis-constructions/prerequisites/01-probability-readers)

## B · Regev statistical-hybrid proofs

| Filled declaration | Check |
|---|---|
| `isUniversal_hash` | Specializing the audited uniform-difference law to zero gives collision probability $1/q^d$ for distinct words. The matrix key space contains the zero matrix, so clearing its cardinality denominator gives an exact collision count of key count divided by $q^d$. The latter denominator is the modular-vector cardinality required by the reader. The differing-bit pivot is a unit even for composite $q$. |
| `uniform_bits_hasMinEntropy` | Each word has mass $1/2^m=2^{-m}$ by `uniform_apply`, the function-space count, and the real negative-power identity. At $m=0$ the unique word has mass one. |
| `strong_leftover_hash` | `leftover_hash` takes those two premises and bounds distance from uniform on the **joint** key/output space by $\tfrac12\sqrt{q^d/2^m}$. At $d=0$ the output space has one element. At $m=0$ the distinct-word condition is vacuous and the denominator is one. |
| `distAdv_hash_uniform_le` | The fiber at a target key and hash value is the singleton key times the words with that hash value. Summing the product-uniform mass gives `hashPair_apply`. The ideal identity sampler has a singleton fiber, giving joint uniform mass. `distAdv_le_statDist` averages over the test’s independent original coins. |
| `uniformKey_uniform_advantage_le` | Augmentation bijectively transposes the sample matrix and appends the public values. The output bijection undoes key augmentation and applies inverse `Fin.snoc` after adding the fixed last-coordinate codepoint. `encrypt_augmented` identifies this relabeled hash sampler with encryption. Uniformity of the ideal key/ciphertext product follows by the same bijection. Both `acceptProb_comp_equiv` steps use the same relabeled test and preserve its original coins. |
| `distAdv_encrypt_le` | The triangle path goes from each real view through its corresponding uniform-key view to the **same** uniform key/ciphertext law. Each real-to-uniform-key edge equals `LWE.decisionAdvantage P χ (reduction P μ D)` with the original sample count and common-secret sampling. The two statistical edges add $2\,\mathrm{extractionError}=\sqrt{q^{n+1}/2^m}$. Extraction uses SIS parameters for the matrix shape alone. |

[Hashing proofs](https://github.com/Shilun-Allan-Li/tcslib/blob/f49ea765eb22ea49c0be978e26741e3b721bb162/TCSlib/Cryptography/Hashing/SIS/Universality.lean#L103) · [Regev proofs](https://github.com/Shilun-Allan-Li/tcslib/blob/f49ea765eb22ea49c0be978e26741e3b721bb162/TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean#L236)

Pei16 §5.2.1, PDF pages 37–39, has the same column-sample key, binary subset sum, uniform-key substitution and final independently uniform key/ciphertext pair. The Lean code uses the frozen floor codepoint, which gives the fixed translation the statistical step needs. The finite constant specializes the repository’s Vad12 strong leftover-hash bound to $q^{n+1}$ outputs and $2^m$ equiprobable words. Lean states the conclusion as a finite advantage bound for each test of two fixed bits. [Pinned Pei16 extraction](https://github.com/Shilun-Allan-Li/tcslib/blob/27f9ea89b72d84abaec8128f2abd826f24aaced4/blueprint/src/references/peikert2016-lattice-survey.raw.md#L1705) · [Owner leftover-hash theorem](https://github.com/Shilun-Allan-Li/tcslib/blob/f49ea765eb22ea49c0be978e26741e3b721bb162/TCSlib/InformationTheory/LeftoverHash.lean#L148)

### Freeze and execution evidence

- The integration relative to the prior intake adds exactly the two owner readers and their four records. The subsequent Lean delta touches only `Hashing/SIS/Universality.lean` and `Encryption/PublicKey/Regev/Experiments.lean`. Six `by sorry` bodies are replaced. The two overviews and the randomized-test and ciphertext sketches describe the implemented routes. The other **151** frozen paths match the integrated baseline byte for byte. The ordered census of **220 declarations in 19 modules** matches the statement freeze, including definitions, imports, options and attributes. The census reconciles the 62 original closed readers, 37 earlier fills and 58 remaining admissions. The earlier `BooleanVector` and `Flat` documentation repairs are present. I found no explicit foreign-definition unfolding, extra handwritten declarations or copied proof infrastructure. This comparison checks frozen source signatures.
- I reconstructed the seven-facade **144-module** import closure. The initial 392.639 s sweep and the nine-module, 24.768 s replay agree with the dependency order, timestamps, source hashes and raw logs. Only the universality reader source changed at replay. The final 397.275 s receipt sums 135 original checks and nine replacements. All **145** final frames, including the 79.380 s final probe, pass their length and hash checks. The 58 owned warnings map to the exact remaining stubs. The 17 inherited admission warnings and 144 other warnings match the prior audit. Three failed development snapshots and the initial unused-instance warning are separately identified. The scoped style result reproduces byte for byte at **0 failures and 2 inherited warnings over 41 files**.
- The final probe has **220 source prints and 58 backing-contract prints**. All six fills use `propext`, `Classical.choice` and `Quot.sound`. Exactly the 58 remaining owned admissions use `sorryAx`. The walk grows from **589 to 593** constants through one `isUniversal_hash._simp_*` and three `distAdv_hash_uniform_le._simp_*` auxiliaries. Every existing name retains its module, kind and privacy status. The two prior `congr_simp` helpers still originate in `DyadicUniform`. [Consumer evidence](https://github.com/Shilun-Allan-Li/tcslib/tree/54c569ae08f723f6caa2bbdb7828a80ada90b16d/briefs/lwe-sis-constructions/fills/06-regev-statistical/evidence)
- I independently reran the final four-module owner and 144-module consumer closures serially with `scripts/lean_check_tree.sh` in separate fresh olean trees. The consumer replay reproduced the warning lists and the final probe byte for byte, including all 278 prints and the 593-constant inventory. The run used fresh manifest-pinned checkouts and a filtered Mathlib cache. After the standard cache command stopped at its ProofWidgets release hook, I used the pinned hash and unpack routines for the 74 external import roots and throttled the retry. Native coverage is limited to the two scoped closures and their probes. The earlier run’s physical cache and freshness provenance are maintainer attestations.

## Continuing notes

| ID | Disposition |
|---|---|
| A1 | The broader InformationTheory facade attempt stopped at the missing Mathlib `NegMulLog` object required by `Entropy`. The six-file owner lint retains 14 inherited failures and two inherited reader warnings. The four-module check and owner verdict cover the `LeftoverHash` closure. |
| A2 | Carry the exact #255 source and records through the target and shared-owner overlap checks. Landing is subject to the user’s merge approval. |
| B1 | Keep scoped source validation, ingestion and approved matching open, including PW10 where consumed. The comparison above covers the fixed-bit hybrid. |
| B2 | Retain the 58 owned admissions and the exact-target landing and export checks for `TCSlib.lean` and the Encoding, LWE, Encryption, SIS hashing and Pseudorandom facades. The consumer proof gate depends on the audited #255 reader source. |
| B3 | Keep the `Randomized.blockVal_eq` hold and the counted-loop registry and host-gate holds, including the applicable head-envelope contract. |
| B4 | Efficient samplers and schedules, uniform asymptotic and message quantifiers, the CPA primitive/game bridge, exact-seed PRG integration, the CRH bridge under independent SIS hardness, all-but-one inversion, strong one-time signatures and final CCA2 remain separate obligations. |

**Notation.** $q$ is the modulus, $d$ the hash output dimension, $n$ the LWE dimension and $m$ the binary word length or Regev sample count. The Lean parameters `P`, `χ`, `μ`, `D`, `p`, `a`, `k` and `α` are the instance parameters, noise, fixed bit, test, distribution, outcome, entropy threshold and hash input type, respectively.
