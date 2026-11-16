# Gate 42 — sc-yao, round 2

**Verdict: CLEAR. G42-01, G42-02 and G42-03 are closed. No new finding or mathematical gap identified.**

| Severity | Open findings |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 0 |

Audit of [draft PR #341](https://github.com/Shilun-Allan-Li/tcslib/pull/341), 16 November 2026. Dispatch and merge remain with Seyoon. Integration with #331, #338 and #339 remains a maintainer merge condition, outside this audit.

| Material | Pin |
|---|---|
| Exchange | `0ddfda335430e259091127a3f62f8b5ea75f2f45` |
| Audited Lean head | `355a0288d56290e8c984228cbc1824187029e456` |
| Campaign records | `2da7e0f3cd65ec93ed71813b7828c3b66ba18942` |
| Round-1 Lean head | `e9b03c437aca251846430ff23b40ee5ff3d3347a` |

**Verification and limits.** I checked all 15 pack SHA-256 entries, all 70 manifested entries of `verification-r2.zip`, and all 989 entries of the separately retrieved integration ZIP, including exact archive path sets. I also verified the round-1 pack's 22 manifest entries against its exchange pin; its `pack.md` is unchanged. The integration ZIP hashes to `4d24501bca1d67a8cf8905448acb77b161a61a45e8d38f72f14dea2fca95d6d8`. All 29 bundle sections match their named sources, allowing the bundle's Lean fences and separator newlines. All 262 source-closure files match Git identities at the audited head: 253 equal round 1 and exactly nine change. Both supplied diffs reproduce with nine-character Git abbreviations. The three landing commits form the stated parent chain; their SSH signatures and the records pin's verify under the same ed25519 key, and a tampered payload fails verification.

This is a re-audit of the changes and their integration evidence. I independently recounted and checked the supplied build, state, axiom and seal artifacts; **I did not run a fresh Lean build or new seals.**

**Round-1 findings.** Helper paths are relative to `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/`.

| Finding | Prior severity | Result | Evidence and assessment |
|---|---|---|---|
| G42-01 | Major | **Closed** | `26f0b77b` changes only `RunWithHost.acc_poly` and its disclosure. The statement and imports are byte-identical. The committed `Eq.trans`/`funext` proof identifies the predicates through `acc_eq` and `Complexity.StateLoop.MajLoop.acc_eq`, lifts the equality to singleton-valued functions, rewrites by that local equality, and applies public `MajLoop.acc_poly`. Neither `acc` definition is unfolded. The docstring explicitly discloses reuse. The committed body, rather than the untried `simpa` fallback, is source-bound to the successful build and all four seals. |
| G42-02 | Minor | **Closed** | `3e99eb80` inserts the full AB09 entry in `ChunkScanner` and BMR90 entry in `GarblingProgram`. Authors, titles, publication information, year and BMR90 pages 503–513 are correct; AB09 §6.2 concerns uniformly generated circuits. Both insertions lie inside module docstrings. Comment stripping gives identical code, and deleting the inserted lines restores each parent byte for byte. |
| G42-03 | Minor | **Closed** | `355a0288` inserts 56 comment lines in exactly the six requested proofs. All additions are whole `--` comment lines. Comment stripping gives identical code, and removing the additions restores each parent byte for byte. The sketches are unchanged. The comments accurately describe the following proof blocks, as detailed below. |

The citation checks used the [Cambridge publication record](https://www.cambridge.org/core/books/computational-complexity/3453CAFDEB0B4820B186FE69A64E1086), [Cambridge contents](https://assets.cambridge.org/97805214/24264/toc/9780521424264_toc.pdf), the [authors' circuit chapter](https://www.cs.princeton.edu/courses/archive/fall07/cos433/circuitschap.pdf), and [BMR90's author-hosted paper](https://www.cs.ucdavis.edu/~rogaway/papers/bmr90). BMR90's wire masks and four indexed gate labels support the row-order attribution.

| Proof | Step comments | Agreement with code and sketch |
|---|---:|---|
| `yaoHybrid_polyTime` | 8 | Alice's garbling and history layout; Bob's total evaluator and history layout; the efficiency characterization; both OT input machines; the answer-independent message envelope. |
| `SelectedLaw.acceptProb_fill` | 7 | Tape/challenge coordinate equivalences, matched exchange, original/filled seed readers, and the two probability transports followed by the exchange law. |
| `FakeSimulatorFactory.exists_data` | 3 | The fully supplied data constructor and its answer-word and message-word equations. |
| `SeedCoordinates.pick_iff_place` | 4 | Key/key, both impossible mixed cases, and nonce/nonce reduced to the published inverse contract. |
| `FakeProgram.tables_poly` | 7 | Program pieces and efficiency, indexed assembly, context transport, canonical lookup, fan-in normalization, and row identification. |
| `BobIO.outputBit_poly` | 6 | Context projections, vertex/key/pair lookups, comparisons and branching, then agreement with `outputBit_eq` on every raw word. |

**Frozen scope.** Masking the six approved regions and LE-title's title line makes `Yao.lean` at the base and head byte-identical. Its frozen headers, definitions and statement prose are preserved, including `yaoSeed_good_whp`. Round 2 adds only 16 comment lines within the approved `yaoHybrid_polyTime` body. The file has **1,195 lines**, within the **1,200** cap, and maximum width 99. `Uniform.lean` equals round 1, retaining exactly its seven approved readers; `DAGCircuit.lean` equals the tip. Across the 70 PR files, only `acc_poly` has a code change since round 1. No new declaration, definition, import or admission was introduced. The recorded lint has zero failures and the same two accepted/inherited warnings.

**Integration and binding.** I reproduced both trees with `git merge-tree --write-tree`:

| Integration | Parents | Reproduced tree |
|---|---|---|
| M (`e327a5f2`) | `f22e0f67`, `e9b03c43` | `741bafe2ce706adbf697ab893bf4bc28e7eb1d7d` |
| M′ (`061ad60c`) | `f22e0f67`, `355a0288` | `84c5381ba7188069f296f899efff9104f9b9bbe0` |

The M → M′ raw diff equals the round-1 → round-2 raw diff, including blob identities, on exactly nine paths. The code diff from `201bf57a` to M′ equals the PR's 70-path diff from `f9fda8fe`. The records pin has the same code/toolchain paths as `f22e0f67`.

| Check | Re-audit result |
|---|---|
| M build | **772/772** records have rc 0 and zero errors. All source hashes match M's blobs; all raw log hashes match their records. The built set is exactly the required downstream set, including root and both audit `Checks`. |
| M′ build | **20/20** records have rc 0 and zero errors, exactly the downstream of the nine changed files. Source/log bindings verify. Zero admissions; one existing `BobIO` warning, now line 218. |
| State | **1,410/1,410** at both trees. I independently recomputed every import-closure key, checked the exact root/audit closure and import order, and matched state object hashes to build records and state-check output. |
| Admissions | **229 → 227**, with M and M′ equal per module. The sole decrease is `Yao` 2 → 0; every PR module has zero. |
| Axioms | At M′ the four Yao results, `yaoSeed_good_whp`, `hbcSecure_compose` and `acc_poly` have only `propext`, `Classical.choice`, `Quot.sound`; their recorded admission traces are empty. `yaoProtocol_hbcSecure` is now standard. The ten `otProtocol_*` results are standard at M. All 1,492 owner-census axiom rows remain standard and identical between M and M′. |
| Yao seals at M | Canonical coe A: **3,046 requests, zero errors**. Coe B: **3,047 requests, 24 errors** in the same nine declarations. Removing the harness restores M's source; raw logs equal round 1 after the probe-directory rename. The existing `PolyExpr.eval` attribution therefore persists. |
| `RunWithHost` seals at M′ | Coe A / strict A / coe B / strict B: **844 / 844 / 845 / 845 requests, zero errors each**. Probe, manifest and run hashes agree; removing the hash-checked harness insertions restores the audited file byte for byte. Install/EOF records are present. `MajLoop.acc` is sealed in all four variants, with `acc_poly` its only recorded term reader. |
| Restore | Pre-snapshot, post-snapshot and independent recheck are byte-identical (`457ba704…`). |

**No seal rerun is necessary.** Yao and the seven other comment-only files were not re-sealed at M′. Their executable source is unchanged, their inserted comments can be removed byte-exactly, and all imported declaration types, definitions and imports remain unchanged. The changed opaque theorem proof is covered by its own four refreshed seals and the downstream rebuild. These facts suffice to carry the earlier seals forward; they do not establish that fresh seals were run on those eight files.

**Round-1 confirmations.** All remain valid, with the improved real-protocol axiom result above:

| Confirmation | Round-2 assessment |
|---|---|
| Efficiency | Both strategies, OT input machines, arbitrary-word/history contracts and answer-independent envelope persist; `acc_poly` now supplies the same contract by public reuse. |
| Statistical simulation | The same bad-seed event, correctness theorem and actual-tape equivalences remain in force. |
| Exact endpoints | Coin relabelling, stage zero and ideal endpoint proofs are unchanged; no uniform-permutation replacement was introduced. |
| B1 / Gate 27 (1)–(5) | All-occurrence enumeration, both slice shapes, identical advice, symbolic separation, reconstruction, polynomial bounds and non-adaptive challenges persist. |
| Quantifiers and error | Simulators precede the distinguisher; one worst advice choice per parameter and averaging remain valid. The total bound remains `δ(n) + 2S(n)|μ(n)|`; edge cases add no hypothesis. |
| Sources | The Lindell–Pinkas architecture and disclosed deviations persist. No fabricated tag or PS10 locator was introduced. |
| Frozen files and earlier landing edits | All preserved, including the 76 Yao declarations, seven Uniform readers, hub/helpers, LE-bullet/reuse/title/doc and documentation of all 739 new public declarations. |
| Rule 10 / historical build | The earlier 718/718 build, 68/68 canonical helper seals, paired controls, four inherited Uniform errors and explicit-unfold assessment remain applicable. The new evidence checks the changed proof and integration separately. |
| SY-F grades | SY-F01 resolved; SY-F02 accepted under DL-51; SY-F03 under DL-49 with the `d6fe1ddd` wording; SY-F04 fixed; SY-F05 fixed/remainder DL-52. SY-F06's G42-01 and SY-F09's G42-03 are now closed. SY-F07/08/10/11 remain notes; SY-F12 remains the accepted size exception. |

**Disclosure assessment.** No additional undisclosed change or necessary-evidence omission identified. The pack correctly discloses the inaccurate M′ parent shorthand in the decision log/PR description: its parents are the records tip and final head, while its build used M's built state. The signature caveat concerns missing local signer configuration; independent cryptographic verification succeeds. The “all 68 helpers” seal claim refers to round 1; only `RunWithHost` was re-sealed at M′. The abbreviated Uniform path, staging tense, stale REST base SHA, scoped lint and deleted raw directories are disclosed, with the required archived evidence available. They introduce no new audit finding. The accepted rulings and DL-49/51/52 are unchanged by the three edits.

**Notation:** M and M′ are the integration trees above; `n` is the security parameter; `S(n)` is the circuit-size bound; `δ(n)` is the negligible bad-seed bound; `μ(n)` is the negligible B1 reduction bound for a fixed distinguisher.
