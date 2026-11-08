**lwe-sis-dyadic-arithmetic-proofs-findings.md**

**Verdict: PASS for the frozen dyadic scalar arithmetic proof gate.**

**Totals: 0 blockers, 0 majors, 0 minors, 3 continuing notes.**

I reviewed all twelve filled proofs, eighteen unchanged declarations, adjacent sketches, the complete owned inventory, and sixteen backing contracts. No mathematical defect, interface drift, prohibited unfolding, unsafe dependency, or unsupported proof-completion claim was found.

This was a static proof audit with independently executed integrity, source-comparison, inventory, dependency, and style checks. **I did not rerun Lean.**

| Item | Verified identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange commit | `083448cef9229dc95b96ef45686ce7f3768992ab` |
| Statement freeze | `dbacd91218c19f0df106d316ce4ff0e22b869e66` |
| Filled Lean/root | `ec72ed773a690c17ac253707350935cc9e0acb34` |
| Bundled records | `a9b97213c616ef7afe80dcaa57eb5a503cf6b110` |
| PR / target | [#239](https://github.com/Shilun-Allan-Li/tcslib/pull/239) / `cryptography/lwe-sis-constructions` |
| Audited dependencies | PRs #236, #237, #238 |
| Bundle SHA-256 | `a252af465a90beab319c27c32b25edafe712f8f105d7969f71b2cbeb98b692d4` |
| Bundle bytes / sections | 6,699,026 / 1,301 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order, followed the first-section pack, and read the policy, workflow, campaign plan, all seven earlier findings reports, and their separate dispositions.

All five exchange checksums pass. Both revision-qualified indexes agree exactly in order, revision, path, size, and hash. Every section matches its indexed bytes; **all 102 source attachments and 1,199 records attachments match their pinned revision/path Git blob identities**.

All nine nested checksum sets pass: 130 current proof-evidence entries and the retained sets of 126, 146, 199, 174, 106, 86, 82, and nine entries.

Source comparison confirms:

- Exactly the twelve previously admitted theorem bodies changed.
- All eighteen ordered declarations, definition bodies, signatures, imports, options, namespaces, and attributes remain fixed.
- The three complete `_eq` readers remain `rfl`, without new simp attributes.
- All 101 other frozen paths remain byte-identical.
- Across the library Lean trees, only `Encoding/DyadicArithmetic.lean` changes.
- Only the module overview changes among comments; declaration prose and sketches remain unchanged.

The statement snapshot matches its original Git blob. This establishes source invariance; it is not an independently reproduced elaborated type-hash comparison.

Locations below refer to the pinned [DyadicArithmetic.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/ec72ed773a690c17ac253707350935cc9e0acb34/TCSlib/Cryptography/Encoding/DyadicArithmetic.lean).

| Operation | Filled proofs | Assessment |
|---|---:|---|
| Addition, lines 87–141 | 4 | Canonical writer, unconditional raw-input width, residue-ring reading, and polynomial-time composition are correct. |
| Multiplication, lines 171–224 | 4 | Canonical multiplication and low-bit writing support all four claims without operand-fit assumptions. |
| Subtraction, lines 269–360 | 4 | Modulus construction, right normalization, subtraction bound, ring interpretation, and polynomial-time composition are correct. |
| **Total** | **12** | **All audited obligations reviewed; no remaining source admissions.** |

Addition and multiplication first convert each operand to exactly `Nat.bits (listToNat operand)`. This supplies the canonical inputs required by the public arithmetic pair equations, including empty words and leading zeros. The reverse writer then gives the stated fixed-width numeral. The residue proofs correctly remove the remainder under the cast and apply the addition or multiplication cast equation.

Every raw-input length proof applies `fromLEPoly_length` to a reconstructed valid pair and reads its first projection. Consequently malformed original pairs require no additional premise.

For subtraction, let
\[
A=\texttt{listToNat a},\quad B=\texttt{listToNat b},\quad
k=\texttt{p.eval u.length},\quad q=2^k.
\]
The modulus word has value \(q\), and right normalization has value \(B\bmod q\). Thus the canonical writer receives the natural number
\[
A+q-(B\bmod q).
\]
The proof explicitly establishes
\[
q>0,\qquad 0\le B\bmod q<q\le A+q,
\]
before using `Nat.cast_sub`. The subsequent cast equations remove the added modulus and the right remainder, yielding the intended ring difference. Width zero gives \(q=1\); no nontrivial-ring or operand-fit hypothesis is needed.

All three complexity proofs construct the claimed functions by public composition, pairing, conversion, arithmetic, and writing contracts. Their final equality transports use function extensionality applied to the complete owner-side `_eq` readers. Subtraction generates its modulus with a constant singleton followed by polynomially many zero bits. Its binary length is polynomial; no exponential unary modulus or runtime arbitrary-polynomial evaluator is introduced.

The sixteen backing contracts were checked in their source and reconciled with their raw axiom prints:

| Owner | Contracts, omitting the common `polyTimeComputable_` prefix where applicable |
|---|---|
| `Complexity.BinArith` | `reverse`, `normBits`, `add`, `mul`, `sub` |
| `EnsembleLemmas` | `zeros` |
| `Complexity` | `pairDropPoly`, `pairFstD`, `pairSndD`, `const` |
| `PolyTimeComputable` | `comp`, `pairEncode`, `append` |
| `Encoding.BinaryArith` | `toLE`, `normalizeWidthPoly`, `fromLEPoly` |

The proofs and sketches agree. No foreign definition is explicitly unfolded, and no helper declaration, private host, or copied proved infrastructure is added. PS10 §2.1 and AB09 §7.2 remain contextual citations for disclosed repository adaptations.

The raw probe and structured inventories reconcile:

| Check | Result |
|---|---:|
| Owned constants using only standard axioms | 302 |
| Earlier constants retaining identity and exact axiom sets | 284 |
| Statement-era constants retaining module, kind, and visibility | 302 |
| Explicit source/backing-contract axiom prints | 18 / 16 |
| Owned constants containing `sorryAx` | 0 |
| New compiler auxiliaries or unexplained constants | 0 |

Every current axiom set is contained in `propext`, `Classical.choice`, and `Quot.sound`. The historical 302-constant statement inventory and 284-constant adapter inventory also agree with their retained raw output.

I reconstructed the exact five-facade, 94-module dependency closure and verified its topological order, source hashes, raw logs, and serial execution records. They reconcile to zero errors, zero owned admissions, seventeen inherited admission warnings, and **251.162 seconds of recorded module time**. The separate probe records **41.336 seconds**.

All three development snapshots match their recorded hashes and passing logs, with admission counts eight, four, and zero. Final development run 02 exactly matches the filled source. These records remain separate from the fresh final sweep.

I reran all five scoped style checks: **0 FAIL / 2 unchanged WARN over twenty files**. The filled module is 362 lines. The fifteen manifest package pins remain unchanged. No finite model was rerun for this body-only fill.

Physical package/cache provenance, isolation, actual object freshness, and native execution remain maintainer attestations. Neither the supplied evidence nor this audit establishes whole-library root elaboration.

| ID | Severity | Location | Evidence / finding | Required follow-through |
|---|---|---|---|---|
| N01 | Continuing note | `policy.md` §2; source-validation records | Full frozen-primary validation, reference ingestion, and approved matching remain open. Shared registry and probability-reader proposals remain unapplied. | Preserve earlier reports and complete the applicable source-policy work. No scalar proof correction identified. |
| N02 | Continuing note | `fills/03-dyadic-arithmetic/evidence/`; integration records | The twelve scalar admissions are discharged in the reviewed fill. This reviewer did not rerun Lean; seventeen inherited warnings, native/cache/isolation attestations, and applicable landing checks remain. | Retain these limits and perform the relevant integration checks. |
| N03 | Continuing note | Sampler, schedule, matrix, and primitive consumer gates | Actual-law sampling, implemented schedules, common-secret sample quantifiers, uniform negligible message bounds, raw collision semantics, matrix implementations, and primitive bridges remain separate obligations. | Carry these into their consumer gates. These scalar proofs establish no cryptographic hardness or completed security endpoint. |

**PASS closes only this frozen proof gate and approves no merge.** No repository source or records were edited, proofs filled, workers dispatched, pushes performed, or merges made.

Notation glossary: \(A,B\) are the operand values; \(k=\texttt{p.eval u.length}\) is the output width; \(q=2^k\) is the modulus.
