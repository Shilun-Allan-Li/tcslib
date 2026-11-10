# Gate 15 counted-loop consumers and SIS collision resistance

Draft [#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250) targets
`cryptography/lwe-sis-constructions`. The proof-only commit fills
the nine remaining admissions in the combined statement wave.

| Pin | Revision |
|---|---|
| Gate 13 Lean and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Gate 13 comparison records | `f4b1e343061101565e9ac93b517d93fec6c4ded3` |
| Gate 14 passed intake | `e953e8c4bb9d2d27bacbbeb46977e665138ced72` |
| Approved H16 registry | `2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11` |
| Checked Lean and root | `8b3187bdaf0c634c086313a727a7210dca14bfeb` |
| Relocation checkpoint | `b5dbc93a769314beec7e7329272bce2a50ea7976` |
| Central preview target | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |

| Scope | Result |
|---|---|
| `Encoding.BooleanVector` | Build the scheduled bit-expansion evaluator from the registered counted loop. |
| `Encoding.DyadicLinearAlgebra` | Build the packed dot product, its scheduled wrapper, one matrix row step, and the scheduled matrix-vector evaluator. |
| `Hashing.SIS.CollisionOutput` | Build the signed collision-output postprocessor for all raw outputs. |
| `Hashing.SIS.Implementation` | Compose bit expansion and matrix-vector evaluation to obtain the hash evaluator. |
| `Hashing.SIS.Asymptotic` | Use one parameter-aware solver and transport its coins to bound the raw collision probability pointwise by SIS success. The dyadic profile supplies the numerical premises. |

The four direct loop consumers use the existing context-preservation and growth
lemmas and the H16 contract. The growth coefficient eight gives length
envelope coefficient nine and degree two. The three other efficiency
proofs compose public contracts and read the defining equations. The two
security proofs preserve the typed coin word under the existing reduction
and use the independent `SISAssumption`. The five module overviews
now describe the filled proofs. The hash evaluator's sketch names the
proved polynomial-time contracts. The wave changes only the nine bodies
and those documentation passages.

| Verification | Result |
|---|---|
| Source freeze | 220 source declarations and all definitions, imports and options preserve their audited surface. Exactly nine theorem bodies change across five paths. The other 148 frozen paths match the passed Gate 14 baseline. |
| Native replay | 144 modules across seven facades in 454.945 s of summed module time, with zero errors and zero owned admissions. |
| Replay segments | 100 modules completed before relocation. Verified their source snapshots and objects, then ran the final 44 modules serially in the same fresh object tree. The first interrupted module was rechecked. |
| Inherited diagnostics | 17 inherited admission warnings. All other warning payloads match Gate 13. |
| Axiom probe | 329 explicit prints and 620 inventoried constants in 85.556 s. Each axiom set is contained in the standard Lean axioms. |
| Type probe | All 220 elaborated type and universe parameter representations match Gate 13 in 2.576 s. The full raw probe output is byte-identical to Gate 13. |
| Style | Zero failures and two inherited warnings over 41 files. |
| Merge preview | Tree `6d2744bad4a023158d262bdeb7c50412b0efb4b2` preserves the checked library, registry, root and build pins. |

Lean emits four auxiliaries in `Hashing.SIS.Asymptotic`. `Complexity.NUPPT.coinsCongr.congr_simp` is the congruence theorem, and three private constants are the two match equations and splitter for the SIS success predicate. All 616 Gate 13 constant identities are preserved. Of those, 607 retain their full inventory entries and the nine fills replace `sorryAx` with `Classical.choice`, `Quot.sound`, and `propext`. [Axiom delta](evidence/axiom-delta.json)

| Inherited module under `TCSlib` | Admission warnings |
|---|---:|
| `Complexity.TuringMachine.Simulation` | 1 |
| `Complexity.TuringMachine.Composition` | 3 |
| `Complexity.TuringMachine.Encoding` | 1 |
| `Complexity.ClassP.TimeConstructible` | 2 |
| `Complexity.TuringMachine.Build.Wrappers` | 2 |
| `Complexity.TuringMachine.Build.Loop` | 5 |
| `Complexity.TuringMachine.Build.Primitives` | 3 |
| **Total** | **17** |

The serial replay uses Lean 4.25.0, the existing manifest and this
worktree's own pinned package cache. No new packages were fetched.
The 178 rank cache fingerprints were rechecked. Whole-library elaboration
and the exact-target integration checks remain landing work.
[Cache receipt](evidence/cache-provenance.json) · [Native receipts](evidence/native-checks.json)

Scoped source matching and landing checks follow the independent proof review.
The generic SIS primitive bridge, efficient trapdoor recovery, family-level
security, and the final CPA and CCA2 bridges are separate obligations.

Merge clearance requires a passing Gate 15 review, scoped source matching,
and exact-target landing checks.
