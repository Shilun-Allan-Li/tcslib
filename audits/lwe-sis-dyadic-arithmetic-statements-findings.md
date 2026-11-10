**lwe-sis-dyadic-arithmetic-statements-findings.md**

**Verdict: PASS for the frozen dyadic scalar arithmetic statement gate.**

**Totals: 0 blockers, 0 majors, 0 minors, 3 continuing notes.**

I reviewed all 18 declarations, their complete readers, prose and sketches, the 12 admitted obligations, preservation of the 284 earlier constants, and all 16 backing contracts. No false statement, missing hypothesis, material API defect, prohibited dependency, or unsupported completion claim was found.

This was a static mathematical audit with independently executed integrity, source-comparison, inventory, dependency, style, and finite-model checks. **I did not rerun Lean. All 12 obligations remain admitted.**

| Item | Verified identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange commit | `1ac4e2e45df94d0b5f20259218d067843458c770` |
| Frozen Lean/root | `dbacd91218c19f0df106d316ce4ff0e22b869e66` |
| Mathematical module commit | `11ec6c1c19deef1bcbd5d4ed2c30207e8abd12a7` |
| Bundled records | `8e460ea0fd620106cff44ef9b0946f50eb2bb50e` |
| Audited stack baseline | `8627edde9892607a699cf997c8dd5a8a2a700e26` |
| Draft branch / target | `cryptography/lwe-sis-dyadic-arithmetic` / `cryptography/lwe-sis-constructions` |
| Audited dependencies | PRs #236, #237, #238 |
| Bundle SHA-256 | `da9d49e247a396f513dc74d3183e11e5d8b271e67947916b0ae0460aaa0537e9` |
| Bundle bytes / sections | 6,189,307 / 1,154 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order, followed the first-section pack, and read the policy, workflow, campaign plan, all six earlier findings reports, and their separate dispositions.

All five exchange checksums pass. Both revision-qualified indexes agree exactly in order, revision, path, size, and hash. Every section matches its indexed bytes, and **all 102 source attachments and 1,052 records attachments match their revision/path Git blob identities**.

All nested checksum sets pass: 126 current entries and the retained sets of 146, 199, 174, 106, 86, 82, and nine entries.

Locations below refer to [DyadicArithmetic.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/dbacd91218c19f0df106d316ce4ff0e22b869e66/TCSlib/Cryptography/Encoding/DyadicArithmetic.lean).

| Operation | Declarations / admissions | Assessment |
|---|---:|---|
| Addition, lines 63–120 | 6 / 4 | Canonical conversion supports the public adder equation. The unconditional writer, raw-input width, residue-ring reading, and FP sketch are sound. |
| Multiplication, lines 125–182 | 6 / 4 | Canonical conversion supports the public multiplier equation. Low-bit writing handles arbitrary operand lengths; the width, ring, and FP statements are sound. |
| Subtraction, lines 187–265 | 6 / 4 | Right-operand normalization and modulus addition correctly prevent natural underflow. The exact writer expression, width, ring reading, and FP sketch are sound. |
| **Total** | **18 / 12** | **3 definitions, 15 theorems; exactly 3 complete `rfl` readers.** |

All three `_eq` readers reproduce their entire definition bodies. None introduces a simp attribute. Each operation’s four admissions cover its canonical writer, unconditional output length, residue-ring interpretation, and polynomial-time computability.

The conversion theorem supplies exactly `Nat.bits (listToNat w)`, satisfying the arithmetic pair equations’ canonical-input requirements even for empty words and leading zeros. The reverse writer retains the requested low bits; sum and product therefore need no operand-fit hypotheses.

For subtraction, put \(A=\texttt{listToNat a}\), \(B=\texttt{listToNat b}\), \(k=\texttt{p.eval u.length}\), and \(q=2^k\). The body writes the natural number

\[
A+q-(B\bmod q).
\]

The crucial bound is

\[
0\le B\bmod q<q\le A+q.
\]

Thus subtraction does not truncate through underflow, and its natural-subtraction cast is justified. Adding the modulus and replacing the right operand by its remainder preserve the intended ring difference. The adjacent sketch explicitly supplies this argument.

The width-two counterexample is handled correctly: left value zero and right value five produce residue three. Subtracting the unnormalized right value after adding only one modulus would instead produce zero.

All raw-input width statements are correct. Malformed outer pairs use the empty template; malformed inner pairs use zero operands while retaining the outer template. The resulting scalar outputs are zero words at the appropriate width. Width zero is allowed and gives `ZMod 1`. Templates need no unary convention.

The three FP sketches compose the actual public projections, conversions, pairing, arithmetic machines, and width writer. Subtraction constructs its modulus as `[true]` followed by polynomially many zero bits, giving polynomial bit length. Each polynomial is fixed before machine selection. No new host, conditional `Candidates.ArithmeticFP` assumption, or foreign-definition unfolding is needed.

PS10 §2.1 and AB09 §7.2 are accurately presented as representation/model context for repository adaptations.

Independent source comparison confirms that the complete baseline-to-source change contains exactly the new module and the Encoding facade’s import/contents additions. **All 100 other frozen paths are unchanged.** Root exports, owner APIs, toolchain, manifest, and shared proposals remain fixed.

The raw probe and structured inventories reconcile:

| Check | Result |
|---|---:|
| Earlier constants retaining module, kind, visibility, and exact axiom sets | 284 |
| New constants, exactly matching the source declarations | 18 |
| Total owned constants | 302 |
| Constants containing `sorryAx` | Exactly the 12 disclosed obligations |
| New compiler auxiliaries or unexplained constants | 0 |
| Explicit axiom prints checked | 34 |
| Backing contracts with only standard axioms | 16 |

The historical raw inventory also agrees with the retained 284-constant inventory. Every non-admitted owned constant uses only `propext`, `Classical.choice`, and `Quot.sound`.

I reconstructed the exact five-root, 94-module dependency closure and verified its topological order, source hashes, raw logs, and recorded outcomes. They reconcile to zero errors, 12 new and 17 inherited admission warnings, and **212.139 seconds of recorded module time**. The separate probe records 30.383 seconds. Development and preflight evidence remain distinguishable from the final sweep.

I reran all five scoped style checks: **0 FAIL / 2 unchanged WARN over 20 files**. All 15 declared package pins agree with the manifest; the disclosed physical copy scope is eight package directories.

I also:

- Reran the supplied finite model, exactly reproducing its **630,831 scalar-operation comparisons**.
- Ran an additional model with aligned pair parsing and bitwise arithmetic: **119,344 scenarios / 358,032 operation comparisons**, including **51,968 malformed-input scenarios**.

These models passed. They supplement the mathematical review; they neither execute Lean nor establish the general statements or complexity bounds. Physical package/cache provenance, isolation, and fresh native execution remain maintainer attestations. No whole-library root elaboration is established.

| ID | Severity | Location | Evidence / finding | Required follow-through |
|---|---|---|---|---|
| N01 | Continuing note | `policy.md` §2; source-validation records | Full frozen-primary validation, ingestion, and approved matching remain open. Scoped inventories and contextual citations do not close them. Shared registry and probability-reader proposals remain unapplied. | Preserve earlier findings and complete the applicable source-policy work. No scalar statement correction identified. |
| N02 | Continuing note | Current execution evidence; integration records | Supplied evidence reconciles, but this reviewer did not rerun Lean. Twelve scalar admissions, 17 inherited warnings, native/cache/isolation attestations, and applicable landing checks remain. | Discharge the 12 obligations through a separately reviewed proof fill and retain the stated verification limits. |
| N03 | Continuing note | Sampler, schedule, matrix, and primitive consumer gates | These scalar statements do not complete actual-law sampling, implemented schedules, common-secret sample quantifiers, uniform negligible message bounds, raw collision semantics, matrix implementations, or primitive-security bridges. | Carry those obligations into their consumer gates. No hardness or completed security endpoint follows from this pass. |

**PASS closes only this frozen statement gate and permits its later proof phase. It does not approve a merge.** No repository source or records were edited, proofs filled, workers dispatched, pushes performed, or merges made.

Notation glossary: \(A,B\) are the two MSB operand values; \(k=\texttt{p.eval u.length}\) is the output width; \(q=2^k\) is the modulus.
