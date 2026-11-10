# Regev statistical hybrid proof fill

The six proofs at `f49ea765eb22ea49c0be978e26741e3b721bb162` use the two approved owner readers on draft #255.
The integrated baseline is `22f4d3c2e6ab01ad85698eed156d3728fc259362`, which
combines the previous audited #250 intake `bb9ab16e363330f2e0384d128f5d208ca6d760bb`
with #255 records `6d9d46b5800e3cde7e89eee6b9d712db3c8982fd`. Both PRs target
`cryptography/lwe-sis-constructions` at `27f9ea89b72d84abaec8128f2abd826f24aaced4`.
The reader additions are checked separately in
`../../prerequisites/01-probability-readers/`.

The six consumer proofs discharge the collision-count universality, bit-word
min-entropy, strong extraction, randomized test bound, statistical key-and-
ciphertext hybrid, and final fixed-bit advantage. The final bound combines two
DLWE advantages and twice the extraction error. Its two uniform-key views are
compared through one common ideal view. The two earlier proof audits cover 37
other obligations. This fill brings the total to 43 proved and 58 admitted.

Only six theorem bodies and explanatory comments change relative to the
integrated baseline. The audit freeze reconciles the 220 prior declarations
and 151 other frozen paths. The two reader bodies are the approved non-simp
`Iff.rfl` equations in their owner modules. The consumer proofs use the
public probability, extractor and encoding interfaces. The source changes
preserve the toolchain and manifest.

| Check | Result |
|---|---|
| Serial seven-facade closure | 144 final module checks totaling 397.275 s, zero errors, 58 owned and 17 inherited admission warnings |
| Axiom probe | 79.38 s, 220 source and 58 backing-contract prints |
| Owned constants | 593 walked, 58 using `sorryAx`, all six filled proofs standard-axiom only |
| Compiler auxiliaries | 4 new, 0 changes in origin |
| Scoped style | Zero failures and two inherited reader warnings over 41 files |

The initial sweep used a newly empty own olean tree and manifest-pinned
packages. After omitting the unused input `Fintype` instance from the reader,
the nine transitive dependents in the sweep were replayed in dependency order,
starting with the corrected owner module. The final axiom probe uses this
corrected tree. `evidence/` records exact source hashes and
byte-framed raw logs. Development failures are separate and concern the
Finset product notation and two inferred types, corrected in the final source.
Full-library root elaboration and the owner InformationTheory facade are outside
the passing fresh scopes. The owner facade preflight encountered an uncached
Mathlib dependency in `Entropy`. The scoped checks pass for the leftover-hash
closure and the #250 consumer closure.

The fixed-bit finite security bound is available on the draft stack. Efficient
samplers and schedules, uniform asymptotic quantifiers, the CPA game bridge,
remaining #250 admissions and scoped source review are later work. The random-bit
reader, counted-loop registry and host-gate holds remain separate.

**Not yet clear to merge.** The combined audit gives separate verdicts for
#255 and these six #250 proofs. The user controls integration.
