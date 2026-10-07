Input SHA-256: `691ced8681da68a8d6f248e8eed3dc1a5fb86ecbb58ba3cc7d6fb0f58b83da6f`. The received `ch2-epoch34-r2-bundle.md` is 480,926 bytes and contains exactly **12 attachments**, under 12 distinct `## ===== <path> =====` headers matching the advertised manifest. No attachment-count discrepancy.

**FAIL — cumulative open defects across both rounds: 0 blockers / 1 major / 0 minors.** Round-1 finding 1 remains open only for kernel public-surface certification; its axiom, target, and module-coverage components are repaired. Round-1 findings 2 and 3 close. The 11 round-1 notes are retained, with the evidence qualifications and dispositions below; they are not additional blockers or majors.

This report, dated 2026-10-06, reviews the supplement and the specified repairs. The round-1 mathematical confirmations remain frozen. I consulted no repository history, changed no supplied artifact, and did not rerun the campaign. Independently recomputed results below are distinguished from supplied execution evidence.

For isolated checker tests, I used Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, on Linux x86-64, Python 3.12.14, glibc 2.39. The available Lean binary initially reported “failed to locate application.” An auditor-local, per-command `LD_PRELOAD` shim redirects only `/proc/<current-pid>/exe` to `/proc/self/exe`; it changes no Lean proof-checking code. Its C source SHA-256 is `1b5db08f7b4105d445c1228bddfc54dd6e587e70e79f1315eea5c8b8ba4379fa`. The isolated probes are not campaign elaboration. The supplement does not supply the complete campaign source/olean tree; its campaign runs remain maintainer evidence.

1. **[major; round-1 finding 1, narrowed] Pass 3 does not establish the claimed kernel public surface.**

   **Files/declarations:** `audits/programs/ch2-epoch34-R2Axioms.lean`: `R2Audit.ownedModules`, the six `publics*` arrays, `generatedExceptions`, and the `run_cmd` variables `isPriv`, `fromPublic`, and `surfaceBad`; `audits/ch2-epoch34-resolutions.md`, finding 1, pass 3.

   **Argument:** The rejection test is:
   
   ```lean
   let isPriv := privateToUserName name != name
   let fromPublic := pubs.any (fun t => t == name || t.isPrefixOf name)
   unless isPriv || fromPublic || name.isInternal || generatedExceptions.contains name do
     surfaceBad := surfaceBad.push name
   ```

   A name being a descendant of an allowed name does not establish that Lean generated it from that declaration. An ordinary, explicitly declared public theorem can have that name. Absence of anonymous instances does not prevent this.

   I compiled an isolated imported module containing exactly these two public source declarations and no anonymous instances:

   ```lean
   namespace SurfaceProbe
   theorem a : True := True.intro
   theorem a.extra : True := True.intro
   end SurfaceProbe
   ```

   Applying the supplied predicate with `pubs = #[SurfaceProbe.a, SurfaceProbe.b]` and no generated exceptions produced:

   ```text
   SURFACE SurfaceProbe.a: private=false, internal=false, fromPublic=true
   SURFACE SurfaceProbe.a.extra: private=false, internal=false, fromPublic=true
   EXPECTED=[SurfaceProbe.a, SurfaceProbe.b]; OBSERVED_COUNT=2;
   EXPECTED_COUNT=2; BAD=[]; b_EXISTS=false
   SurfaceProbe.a.extra : True
   ```

   Both compilation commands exited 0. Thus an unlisted public theorem passes, an expected declaration can be absent, and equal public counts do not detect the substitution. The current program contains no reverse existence/ownership check for every entry of the public lists. The 21 target checks establish existence for those targets, not for all 45 public-list entries.

   There is also an independent broad exemption: Lean's `Name.isInternal` is a naming test, not a certificate of generated provenance or `private` visibility. An ordinary public `Complexity._auditR2Extra : True` passed an additional isolated test. Finally, printing the fixed `generatedExceptions` array does not verify that each item exists in its asserted owning module or is the disclosed generated artifact.

   This challenges the certification procedure, not the frozen mathematics: I do not claim either probe declaration occurs in the campaign. The supplied lint counts agree with the list lengths, but those counts do not supply the missing name-by-name comparison. Consequently “kernel surface = the source publics” and the resolutions' assertion that prefix descent is sound are not established by this repair. The required public-surface part of round-1 finding 1 remains a major evidence gap.

   **Proposed resolution:** Append a per-module inventory of actual non-private kernel names, including the currently exempt internal names. Check exact membership against the source public declarations and an explicitly reviewed generated-name inventory, or validate generated ancestry using appropriate metadata. Check expected source declarations for existence and correct module ownership. Bind each of the 11 disclosed exceptions to its actual module and generating declaration/type. Remove unrestricted prefix/internal-name acceptance as a substitute for this verification, and rerun against the pinned final snapshot. No frozen target statement or owned proof needs changing.

2. **[note; round-1 finding 1, partial closure] The axiom, target, and advertised-module coverage repairs address the original counterexample.**

   **Files/declarations:** `audits/programs/ch2-epoch34-R2Axioms.lean`: `allowed`, `clean`, `visit`, `userRoots`, `targets`, `orderModules`, and passes 1, 2, 4, 5; `audits/logs/ch2-epoch34-r2-axioms.log`.

   **Argument:** I independently counted 21 distinct targets and verified exact agreement with the 21 logged empty-root rows. The program applies `collectAxioms` to each. I counted 65 distinct order entries and verified their ordered equality with both the manifest and fresh sweep. Pass 5 tests inclusion of each entry; the restored six-umbrella import set includes the previously omitted branch.

   The new walk inspects checked declaration types, values including opaque bodies, and inductive constructors. These are the relevant dependency cases used by the pinned Lean `CollectAxioms` implementation. It rejects any `axiomInfo` outside the permitted triple. In an isolated imported module, the copied walk returned `false` for both an unused private `axiom ... : False` and a private theorem depending on it. A missing-name probe returned `false`, printed the panic, and exited 1 when passed through the rejection branch. The old silent-success counterexample is repaired.

   The provisional `true` cache entries break recursive dependency cycles. They should not be read as independently proved per-name results while traversal is in progress. They do not conceal a bad axiom from a successful whole run: its first discovery returns false, which propagates along the active calls to an enumerated root; that root is retained in `tcslibBad`, causing rejection.

   The log's six owned-module totals sum to
   `820 + 490 + 786 + 41 + 439 + 1550 = 4126`.
   Its whole-import total is 11,510, an increase of `11510 − 11436 = 74`. These are consistent supplied runtime counts, not independently reproduced campaign counts. The axiom walk applies before the surface exemptions, so the 11 disclosed generated artifacts receive no axiom exemption.

   **Proposed resolution:** Close the axiom, target, and module-inclusion components of round-1 finding 1. Retain these checks while repairing pass 3 under finding 1 above.

3. **[note; round-1 finding 2 closed] The merge supplement supplies the missing changes and substituted proof implementations.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/merge2-owned-diffs.md`; `SAT.lean`: the five `sat_*` toolkit aliases and their changed callers; `EXP.lean`: `enumWord`, `enumCont_verifier_call`, `enumCont_clean_verifier`, `enumCont_from_body`, `enumMachine_contracts`, `exists_proj_decider`, `NP_subset_EXP`; `PolyTimePairing.lean`: `polyTimeComputable_of_linear`, `polyTimeComputable_const`, `polyTimeComputable_ite`, `polyTimeComputable_and`; `Composition.lean`: `bufferedCompTM_computesInTime`, `exists_comp_on_image`.

   **Argument:** I parsed every supplied diff hunk and checked its old/new line counts and cumulative offsets. The independently counted changes are:

   | Diff | Added | Deleted |
   |---|---:|---:|
   | Merge #2, SAT | 46 | 81 |
   | Merge #2, EXP | 171 | 155 |
   | Merge #2 total | **217** | **236** |
   | Merge #1, Tautology | 35 | 39 |

   The SAT aliases retain their former contracts. Linear-time inclusion chooses polynomial degree 1; constants use the existing finite-control emitter. Branching raises the three degrees to their maximum and pays for the test, the larger branch budget, and the constructor's additive overhead. Conjunction is the true branch's second bit and the constant false branch. These substitutions preserve the Boolean behavior.

   The image-only composition proof uses the same buffered machine. Its intermediate length bound is `(f x).length ≤ T₁ x.length`, so the shared timed contract gives:
   
   ```text
   T₁ x.length + (f x).length + 2 + T₂ x.length
     ≤ 2 * T₁ x.length + T₂ x.length + 2.
   ```

   The second budget remains measured at the original input length; the proof does not introduce a totality or monotonicity assumption on the second machine.

   The EXP diff promotes the unchanged fixed-width enumeration function and generalizes the verifier budget to `Tv`. The changed calls evaluate it at the exact assembled length, so no monotonicity of `Tv` is needed. The guarded startup/round interfaces and endpoint configurations are preserved. The replacement common budget pays `3 * Tv` explicitly; the loop assembly retains fuel and startup costs. The final NP specialization bounds both powers by degree `d + c + 1`, using the positive base, before applying the existing exponential normalization. These are the changes under review; the previously confirmed endpoint mathematics is not reopened.

   Merge #1's supplied diff documents the DNF carrier/evaluation substitutions and totals already described in round 1. It supplies the missing change record for note 12. Its historical blob associations, like merge #2's asserted equality to HEAD, remain supplied provenance rather than independently fetched Git objects.

   **Proposed resolution:** Close round-1 finding 2 at the supplied-diff and source-review level. Retain the carrier approval and unchanged mathematical confirmations. The remaining gate failure is finding 1, not an identified merge-proof defect.

4. **[note] The manifest and sweep transcripts are consistent; the historical sweep is not an admission-free final run.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/final-source-manifest.md`; `audits/logs/ch2-epoch34-r2-sweep.log`; `audits/logs/colleague-merge2-sweep.log`; the two supplied shared source modules.

   **Argument:** The manifest has exactly 65 distinct modules, numbered 1–65, with well-formed source and olean SHA-256 entries. Its commit `154ecb189633c08b3a76ce1d0aac74e16e335021` agrees with the fresh sweep's HEAD. Removing bundle framing, I recomputed exact matches for both supplied complete source files:
   
   - `PolyTimePairing.lean`: `31a44bda2c205dfd92903417e636112cf9947222c5d87ab122870f4881cd1c82`.
   - `Composition.lean`: `264430fafd3c760d9d0a9f44207213dbdb20bba87a898f438e9a6b3e5daebc64`.

   The fresh sweep contains the same 65 entries in order, no `error:` lines, no sorry warnings, and the final `SWEEP_OK 65/65` at 20:28:40Z.

   The historical transcript contains 66 attempts: the first 52 modules, the failed old-order module 53 (`TuringMachine`, missing `UnaryTape.olean`), and the 13-module extended-order resume. Its successful modules agree with the final order. It also contains `Tautology.lean:1271:8: warning: declaration uses 'sorry'`. This historical warning is consistent with a later fill; it is absent from the fresh final sweep. The historical `SWEEP_OK` must therefore not be represented as an admission-free final verification.

   Only the two supplied complete source hashes could be recomputed here. The other source identities, all olean hashes, freshness, and the linkage of those oleans to the closure run are maintainer evidence. The supplement now supplies the requested manifest; this qualification does not impose a new requirement to rebuild excluded campaign internals.

   **Proposed resolution:** Retain the manifest and distinguish the historical merge run from the final sweep. Describe campaign execution as supplied evidence and the two source-hash comparisons as independently checked.

5. **[note; round-1 finding 3 closed] The scoped lint repairs the missing Cook–Levin coverage.**

   **Files/declarations:** `audits/logs/ch2-epoch34-r2-lint.log`; module-wide policy coverage for all six owned files.

   **Argument:** All six files now have INFO rows. The five owned size exceptions are explicitly identified: Hardness 9,937; Nondeterminism 5,835; SAT 4,815; EXP 3,268; Tautology 1,749. Snapshot is 368 lines. The separate 1,755-line TMSAT warning is correctly identified as the standing epoch-2 exception.

   The reported public counts, in the closure program's owned-module order, are `8/8/5/14/5/5`, exactly the lengths of its six public arrays. This confirms count agreement, subject to finding 1's name-comparison limitation. The log reports zero FAIL across the two subtree runs. I did not independently rerun the lint.

   **Proposed resolution:** Close round-1 finding 3. Preserve the already approved size exceptions and post-gate retrofit deferral.

6. **[note; round-1 note 4] The deletion arithmetic is repaired; the historical census remains an attestation.**

   **Files/declarations:** `audits/ch2-epoch34-resolutions.md`, finding 4; `final-source-manifest.md`; historical fill-deletion inventory.

   **Argument:** I summed all 12 listed nonzero deletion rows: 22 sorry-line deletions and 76 other deletions. The relationship to the original residual is:
   
   ```text
   98 = 22 + 76
      = (21 + 1) + (34 + 1 + 33 + 8).
   98 − 21 − 34 − 33 = 1 + 1 + 8 = 10.
   ```

   The explanation assigns one extra sorry deletion to the relocated local admission and one splice to the 35-line non-sorry deletion group. The remaining eight are itemized as `1 + 5 + 1 + 1` in commits `bf6a06f8`, `42f99b0f`, `96d5b017`, and `07bbad98`. The numerical residual is fully accounted for.

   These are recomputations of the supplied rows, not verification against commit diffs. The 59-commit classification/no-touch claim remains outside independently inspected evidence. The resolution's assertion that the round-2 manifest “pins those endpoints” is too broad: that manifest names the final run commit, not both census endpoints or the complete census.

   **Proposed resolution:** Accept the arithmetic correction. Preserve the historical-provenance qualification and correct the endpoint wording in a subsequent resolutions record; do not amend the immutable pack.

7. **[note; round-1 note 13] The requested checksum record is present, but its replay and selection claims are maintainer verification.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/duplicate-run-record.md`; `audits/ch2-epoch34-resolutions.md`, finding 13; the selected beta patch and integration `1c824071`.

   **Argument:** The record identifies all three archive deliveries, assigning the duplicate alpha archive the same digest, and provides separate alpha/beta patch digests. It states that replaying beta at `61cf5958` reproduces integration tree `8e1c03588179ae0457ea4b388521aa7bfc43cbe6`.

   This is now an inspectable record of the requested maintainer-side replay. If the stated replay and identities are correct, equality of the complete result trees establishes byte-for-byte equality with beta's replayed result. It does not, by itself, establish alpha's eligibility, comparative economy, or the historical claim that alpha was never applied anywhere. The archives, patch bytes, replay transcript, and object trees are not supplied, so I cannot independently recompute those digests or the replay.

   **Proposed resolution:** Accept provision of the checksum/binding record while retaining round-1 note 13's independent-verification qualification. Label the replay as maintainer-verified. Retain whole-run selection and its approved criterion order; no new gate-blocking defect is inferred from the unavailable archives.

The round-1 mathematical notes and the two approved post-gate deferrals remain unchanged. Closure of this gate requires the public-surface evidence repair in finding 1.

Glossary of probe notation: `SurfaceProbe.a` and `SurfaceProbe.a.extra` are ordinary public test theorems; `SurfaceProbe.b` is an absent expected test name. All other code identifiers retain their meanings in the supplied sources.

