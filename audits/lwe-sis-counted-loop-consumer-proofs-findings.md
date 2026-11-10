# Gate 15 round 1 findings

**PASS** for the seven efficiency proofs and two asymptotic SIS collision-resistance proofs in draft PR #250 of `Shilun-Allan-Li/tcslib`. **0 blockers, 0 majors, 1 documentation minor, 4 continuing notes.** [Draft PR #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250)

## Exact pins

| Item | Revision or value |
|---|---|
| Exchange `exchange/pass-shelat-ch5-8` | `be2117f662dc51da335bebf70c90f14521f8076b` |
| Gate 15 Lean source and root | `8b3187bdaf0c634c086313a727a7210dca14bfeb` |
| Gate 15 bundled records and observed draft head | `e1614b8466eb74f8842b3d6f244ca4ff3bfe1720` |
| Gate 14 passed intake and proof baseline | `e953e8c4bb9d2d27bacbbeb46977e665138ced72` |
| Gate 14 audited head | `a65cc24d64766786fa43f2cc43ca91dbba8076ef` |
| Approved H16 registry | `2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11` |
| Relocation checkpoint | `b5dbc93a769314beec7e7329272bce2a50ea7976` |
| Gate 13 Lean source and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Gate 13 comparison records | `f4b1e343061101565e9ac93b517d93fec6c4ded3` |
| Target `cryptography/lwe-sis-constructions` | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| Recorded merge base | `6d9d46b5800e3cde7e89eee6b9d712db3c8982fd` |
| Reproduced source merge tree | `6d2744bad4a023158d262bdeb7c50412b0efb4b2` |
| Observed GitHub merge ref and reproduced tree | `b8b790c8b5441ef9de97a75d1b6921369cce40b3` · `1da91a108d0efc2e347ba8ef913077b920b93624` |
| Lean and Mathlib | `v4.25.0` (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`) · `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |
| Bundle SHA-256 | `446c3ce5461bed7feee09bfc6989517dbe4716291bd3328d28cc769004a05bcc` |
| Bundle extent | 4,903,860 bytes · 228 sections (153 source, 75 records) |

## Packet and source freeze

All five outer and 42 nested checksums passed. The text and JSON indexes agree in order on every revision, path, byte count and SHA-256. I compared all 228 extracted sections against their Git blobs, including the first-section pack, and the Gate 13 comparison evidence against its original records pin. [Exchange packet](https://github.com/Shilun-Allan-Li/tcslib/tree/be2117f662dc51da335bebf70c90f14521f8076b/lwe-sis-constructions/outbox/gates/15-counted-loop-consumer-proofs-r1)

The source census preserves all 220 declarations across 19 modules in order. Against Gate 14, exactly nine `by sorry` bodies change in five Lean files. Their proof fingerprints reproduce, and the other 148 frozen paths are byte-identical. Separately, the diff refreshes five module overviews and the hash evaluator's sketch. Signatures, definitions, attributes, imports and options agree. Relative to Gate 13, the additional frozen-path delta is exactly the approved H16 row. I verified its preimage and postimage. The full `TCSlib/` tree, registry, root exports and build pins match the checkpoint, records and both merge trees. [Proof commit](https://github.com/Shilun-Allan-Li/tcslib/commit/8b3187bdaf0c634c086313a727a7210dca14bfeb) · [H16 approval](https://github.com/Shilun-Allan-Li/tcslib/commit/2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11)

## Efficiency proofs

Each of the four direct uses supplies a polynomial-time leaf, preserves the entire first projection on every raw state, and bounds one-step growth by `8 * ((pairFstD d).length + 1)`. For every `j ≤ c.length`, H16's `forLoop_bound_of_ctx` bounds `(f^[j] d).length` by `9 * ((pairEncode c d).length + 1)^2`. The wrapper constructs a valid host pair from total projections even when its input is malformed. `forLoop_pairEncode` gives exactly one call per counter letter, including zero calls for an empty counter. Width zero is valid for the word functions, and the counted loop still terminates. [H16 contracts](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Complexity/ClassP/BinaryArith/Loops.lean#L104-L194)

| Fill | Checked composition |
|---|---|
| `polyTimeComputable_expandPoly` | Builds the width template of zeros and unary count from the parameter word's length, initializes empty output, and takes the result projection. Missing source bits default to false. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Encoding/BooleanVector.lean#L184-L201) |
| `polyTimeComputable_dotWords` | Reads the width, counter and two operands from the nested pair. The initial accumulator has exactly the width-word length, so zero steps give the correct zero word. The last projection returns the accumulator. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Encoding/DyadicLinearAlgebra.lean#L152-L172) |
| `polyTimeComputable_dotPoly` | Builds the scheduled width and count, pairs them with the two projected operands, and composes the packed dot proof. The public pair equations discharge the wrapper identity on arbitrary input. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Encoding/DyadicLinearAlgebra.lean#L254-L267) |
| `polyTimeComputable_matVecStep` | `mulU` makes the row cut with length equal to the column count times the width. The `.var` prefix and suffix operations use this exact length, including zero. The step keeps the full width/count/vector context and appends the packed dot result. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Encoding/DyadicLinearAlgebra.lean#L315-L338) |
| `polyTimeComputable_matVecPoly` | Builds the same retained context, initializes the row suffix and empty output, and uses the unary row counter and final projection. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Encoding/DyadicLinearAlgebra.lean#L440-L460) |
| `polyTimeComputable_collisionOutputPoly` | Splits at the scheduled column count with total take/drop, builds the magnitude-width word and unary count, then projects the sign/magnitude output after exactly that many rounds. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Hashing/SIS/CollisionOutput.lean#L281-L300) |
| `polyTimeComputable_hashPoly` | Keeps the parameter and matrix word, expands the projected raw domain word at the same column and residue-width schedules, and passes that expansion to the matrix evaluator at the declared row schedule. [Proof](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Hashing/SIS/Implementation.lean#L84-L98) |

## Asymptotic SIS proofs

1. `rawCollisionInputs` false-pads or truncates to twice the column count and splits there. The postprocessor's `take` and `drop` followed by default-false reads give the same two vectors. It writes sign `!x && y` and magnitude `xor x y`, the signed encoding of the integer difference. Positive magnitude width makes each coordinate fit, and the exact-length decoder returns that difference. For a successful collision the difference is nonzero, lies in the modular kernel, and has squared norm at most the column count. This gives event inclusion on the same matrix and finder coins. [Raw reader and decoder](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Hashing/SIS/CollisionOutput.lean#L182-L319) · [SIS witness](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Hashing/SIS/Basic.lean#L95)
2. `negligible_collisions_of_SIS` uses `NUPPT.exists_compParam` to choose one solver for all parameters. `pairSndD` gives the finder the same encoded matrix argument. The solver retains advice and the coin polynomial, and its postprocessor sees the unary parameter and original finder output. The matrix identity paired with `coinsCongr hcoins.symm` maps finder coins to solver coins and preserves `List.ofFn`. `uprob_comp_equiv` therefore identifies the postprocessed experiment with solver success. At every parameter the collision probability is nonnegative and at most the solver's SIS success probability. The independent SIS hypothesis and `Negligible.mono` yield the result with domination threshold zero. [Reduction](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Hashing/SIS/Asymptotic.lean#L71-L110)
3. `dyadic_collision_negligible` uses `SISAssumption dyadicFamily`. At parameter `κ`, both the exact column count and squared-norm budget are `2*(κ+1)^2`, and the magnitude width is `2*(κ+1)^2+1`. The readers discharge all three premises, including at `κ=0`. [Specialization](https://github.com/Shilun-Allan-Li/tcslib/blob/8b3187bdaf0c634c086313a727a7210dca14bfeb/TCSlib/Cryptography/Hashing/SIS/Asymptotic.lean#L112-L129)

## Replay and Gate 13 comparison

I independently replayed `scripts/lean_check_tree.sh` serially for all 144 Gate 15 modules, then for `ProofAxioms.lean` and `TypeProbe.lean`. I used Lean 4.25.0 on x86-64 Linux and a fresh `TCSLIB_OLEANS` tree with `.lake/build/lib/lean` absent. All 15 package checkouts matched the manifest revisions. The source, archive and object fingerprints for all 178 rank-cache entries reproduced. Every module produced a fresh object with zero errors, and all 144 module logs and both probe outputs matched byte for byte.

For the Gate 13 probes, I rebuilt the eight affected modules at the Gate 13 source pin and reused the other 136 objects from the clean replay, whose sources and imports agree. All eight module logs and both probe logs reproduced. I also replayed the Gate 14 `HeadEnvelope.lean` probe, which reproduced its six axiom prints, and ran 22 supplementary Lean guards using the documented most-significant-bit-first encoding. The guards covered malformed pairs, zero schedules, short and excess raw words, and signed decoding. [H16 probe](https://github.com/Shilun-Allan-Li/tcslib/tree/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/briefs/lwe-sis-constructions/prerequisites/02-counted-loop-registration/evidence)

The exact 144-module order is the same seven-facade topological closure at both pins. The supplied Gate 15 receipts record a 100-module prefix and a 44-module continuation starting at `Encryption/Symmetric/Regev`. I rehashed the 144 module logs and axiom log from each packet. Of the module logs, 139 are byte-identical across gates. The other five lose the nine owned admission warnings and preserve every other diagnostic. Style replay reproduced zero failures and the two inherited check-8 warnings for `DLWEAssumption` and `SISAssumption` over 41 files. [Gate 15 receipts](https://github.com/Shilun-Allan-Li/tcslib/tree/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/briefs/lwe-sis-constructions/fills/10-counted-loop-consumers/evidence) · [Gate 13 receipts](https://github.com/Shilun-Allan-Li/tcslib/tree/f4b1e343061101565e9ac93b517d93fec6c4ded3/briefs/lwe-sis-constructions/fills/09-gadget-inversion/evidence)

All 329 explicit axiom prints reconcile. The inventory grows from 616 to 620, with 607 full entries identical and nine entries changing as described in F01. Lean generates four additions in `Hashing.SIS.Asymptotic`. They are `Complexity.NUPPT.coinsCongr.congr_simp`, two private match equations and the private splitter for `successProbability`. All Gate 15 axiom sets are subsets of `Classical.choice`, `Quot.sound` and `propext`. I compared all 220 elaborated type and universe representations directly. The two raw type logs are byte-identical with SHA-256 `d5f44c33a0a2df3f49a66f29fe9c14319cdf120e85e94e2cf04b7d152a53d663`. [Axiom delta](https://github.com/Shilun-Allan-Li/tcslib/blob/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/briefs/lwe-sis-constructions/fills/10-counted-loop-consumers/evidence/axiom-delta.json) · [Type receipts](https://github.com/Shilun-Allan-Li/tcslib/blob/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/briefs/lwe-sis-constructions/fills/10-counted-loop-consumers/evidence/type-checks.json)

| Inherited module under `TCSlib/Complexity` | Warnings |
|---|---:|
| `TuringMachine/Simulation` | 1 |
| `TuringMachine/Composition` | 3 |
| `TuringMachine/Encoding` | 1 |
| `ClassP/TimeConstructible` | 2 |
| `TuringMachine/Build/Wrappers` | 2 |
| `TuringMachine/Build/Loop` | 5 |
| `TuringMachine/Build/Primitives` | 3 |
| **Total inherited** | **17** |

## Finding and continuing notes

- **F01 · Minor, documentation.** The Gate 15 report describes the three standard axioms as replacing `sorryAx`. All three were already present in each of the nine Gate 13 entries. The exact change is the removal of `sorryAx` from each set. The recorded inventories and delta give the correct evidence. [Fill report](https://github.com/Shilun-Allan-Li/tcslib/blob/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/briefs/lwe-sis-constructions/fills/10-counted-loop-consumers/REPORT.md)
- **N01.** The nine Gate 13 proof obligations close here. The inherited machine-library admissions remain tracked separately.
- **N02.** Scoped reference ingestion and approved matching of the consumed passages remain open, including the PW10 adaptations carried forward from Gate 13. [Gate 13 disposition](https://github.com/Shilun-Allan-Li/tcslib/blob/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/audits/lwe-sis-gadget-inversion-proofs-resolutions.md)
- **N03.** Efficient trapdoor recovery, family-level sampling and security, the generic SIS collision-resistant primitive bridge, and the final CPA and CCA2 bridges remain separate obligations. Strong one-time signatures remain on the CCA2 route.
- **N04.** Whole-library elaboration and the exact-target landing recheck remain conditions for merge clearance. [Source preview receipt](https://github.com/Shilun-Allan-Li/tcslib/blob/e1614b8466eb74f8842b3d6f244ca4ff3bfe1720/briefs/lwe-sis-constructions/fills/10-counted-loop-consumers/evidence/integration-preview.json)

**Notation.** `f` is a loop leaf, `f^[j]` its `j`-fold iterate, `c` the counter word and `d` the body word. `κ` is the security parameter. `x` and `y` are the two bits in one signed output coordinate.
