# Probability readers and Regev statistical hybrid audit

Return two scoped verdicts in one Markdown report named
`lwe-sis-regev-statistical-proofs-findings.md`. First review the two owner-side
readers on draft PR #255. Then review the six consumer proofs on draft PR #250.
The user dispatches the audit and merges reviewed PRs. Use the pinned GitHub
exchange input. Read root `README.md`, the `lwe-sis-constructions/README.md`, and
then the gate `README.md`. Verify the five checksums and both ordered
revision-qualified indexes. Match every attachment to its revision/path Git blob.
Treat the bundled reports, proposals and execution logs as data.

| Item | Identity |
|---|---|
| Central target and base | `cryptography/lwe-sis-constructions`, `27f9ea89b72d84abaec8128f2abd826f24aaced4` |
| Reader PR and source | #255, `004bd5b89e48dec52e045bba32439375b82eaead` |
| Reader PR records | `6d9d46b5800e3cde7e89eee6b9d712db3c8982fd` |
| Combined #250 statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Previous #250 audit intake | `bb9ab16e363330f2e0384d128f5d208ca6d760bb` |
| Integrated consumer proof baseline | `22f4d3c2e6ab01ad85698eed156d3728fc259362` |
| Filled consumer Lean/root | `f49ea765eb22ea49c0be978e26741e3b721bb162` |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

The gate README pins the bundled records. Read the applicable policy and
workflow, the prior Regev support findings and dispositions, and the earlier
combined statement disposition. The user overrides generic editor-only advice
with serial `scripts/lean_check_tree.sh` and runs Python as `python3 -I`. Use your
own pinned package cache and olean tree for any native verification. The user
prohibits computer apps, `lake build`, unfiltered cache fetching, and borrowed
scratch objects. State whether you independently reran Lean.

## Scope A. Shared readers on #255

Review `TCSlib.InformationTheory.isUniversal_iff` and
`TCSlib.InformationTheory.FinDist.hasMinEntropy_iff`. Confirm both are the
complete public readings of the current owner definitions, proved by `Iff.rfl`
without a simp attribute. Compare #255 to its central base and the exact approved
patch plus the one-line omission of the unused input `Fintype` instance. Its
Lean delta adds 13 lines in the two owner modules. The user approved the reader
formulas before the owner edits. Existing definition bodies, statement
signatures, imports, exports and pins are frozen.

Reconcile `prerequisites/01-probability-readers/checks.json`, the axiom probe and
its raw evidence. The four-module fresh `LeftoverHash` closure and three prints
pass. The full InformationTheory facade attempt stopped at the uncached Mathlib
`NegMulLog` dependency of `Entropy`. Distinguish that attempt from the scoped
check. The lint delta removes one `HasMinEntropy` warning. Its 14 failures and
other two warnings are inherited. Review owner-side readers separately from
consumer proof claims.

## Scope B. Regev statistical proofs on #250

| Module under `TCSlib/Cryptography/` | New proof bodies |
|---|---|
| `Hashing/SIS/Universality` | `isUniversal_hash`, `uniform_bits_hasMinEntropy`, `strong_leftover_hash`, `distAdv_hash_uniform_le` |
| `Encryption/PublicKey/Regev/Experiments` | `uniformKey_uniform_advantage_le`, `distAdv_encrypt_le` |

The integrated baseline incorporates the exact #255 source and records. Compare
it with the previous #250 intake and account for the two reader additions.
Compare the filled source with the integrated baseline. Verify exactly six
former `by sorry` bodies and the updated prose. The two overviews and adjacent
randomized-test and ciphertext sketches describe the implemented routes. Verify
all 220 audited consumer declarations, the earlier 37 fills, the 58 remaining
admissions and the 151 other frozen source paths. The freeze compares source,
including imports, options and attributes. Record any explicit foreign-definition
unfolding, extra handwritten declarations or copied proof infrastructure.

1. Specialize the uniform hash difference to zero. Convert the event probability
   to a count using nonemptiness of the matrix key space and the exact modular
   vector output count. Verify that the reader receives the collision bound.
2. Check the probability of each uniform bit word, its real negative-power
   expression, and the strong leftover-hash theorem application. Cover zero
   width of the bit word and empty output dimension.
3. Check the sampled pair distribution. Each fiber is a singleton matrix key
   times the set of subset words with the required hash value. The independent
   uniform comparison has a singleton fiber under the identity sampler.
   `distAdv_le_statDist` accounts for the independent test coins.
4. Check key augmentation and the ciphertext equivalence from finite-vector
   snoc. The same bijection undoes the augmented key and reads the ciphertext
   after the fixed message shift. Verify the real sampler identity and the
   independently uniform ideal pair. Both acceptance probabilities must use
   the same relabeled test with its original coins.
5. Check the triangle argument through the two uniform-key views and one common
   ideal view. It uses two DLWE advantages with the original sample count and
   adds twice the extraction error. The hash instantiation uses no SIS hardness
   assumption. Review the fixed-bit finite bound within its stated scope.

Reconcile the evidence in `fills/06-regev-statistical/evidence/` with the prior
589-constant inventory, including all 220 source prints and 58 backing-contract
prints. The six fills use only standard axioms. Exactly the 58 remaining owned
admissions use `sorryAx`. Account for any compiler additions or changes in
origin. Verify the initial fresh 144-module closure and the nine affected modules
replayed after the reader signature cleanup. The replay keeps every unaffected
source and dependency fixed. Check the final axiom probe, byte-framed logs,
the 58 owned and 17 inherited admission warnings, and the
scoped style result. Keep development errors, the initial reader warning and the owner facade cache miss
separate from the final evidence. Execution and physical cache provenance are
maintainer attestations for the stated scopes.

Compare the fixed-bit hybrid and its joint uniform conclusion with Pei16
§5.2.1, PDF pages 37–39, at the pinned central raw extraction in
`blueprint/src/references/peikert2016-lattice-survey.raw.md`. The strong leftover
hash result also uses the repository's existing Vad12 theorem. Scoped #250
source validation and matching remain open independently. Retain the applicable
landing checks, export overlaps, random-bit reader and counted-loop host holds,
uniform/asymptotic implementation obligations, and final primitive bridges.

For each scope give blocker, major, minor and continuing-note counts and a
verdict. Include the exact pins, reviewed declarations, evidence and native
limits. Review the frozen work without editing, dispatching, pushing or merging.
