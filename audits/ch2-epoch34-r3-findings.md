Input SHA-256: `730760ec419d0bc22003789e5971eb880d679f19e95969f8867f039be0c25456`. The received `ch2-epoch34-r3-bundle.md` is 60,972 bytes and contains exactly **5 attachments**, under five distinct `## ===== <path> =====` headers matching the advertised manifest. No discrepancy.

**PASS — cumulative open defects across rounds 1–3: 0 blockers / 0 majors / 1 minor.** The remaining major, round-1 finding 1 as narrowed in round 2, closes. The sole open defect is the inventory's downstream-unusability wording, described in finding 3 below; it does not invalidate the exact surface certification. All other earlier closures, mathematical confirmations, and deferrals remain frozen.

1. **[closed major] Pass 3 now establishes exact equality with the reviewed per-module inventories.**

   **Files/declarations:** `audits/programs/ch2-epoch34-R3Axioms.lean`: `ownedModules`, the six `inventory*` and `publics*` arrays, and the surface checks in `run_cmd`.

   The argument follows the executable checks:

   - `actual` receives precisely the enumerated names whose recorded owning module equals `modName` and whose names are non-private under `privateToUserName`.
   - Every element of `actual` outside `expected` enters `surfaceBad`; a nonempty `surfaceBad` rejects the run. Thus successful completion implies every actual name is expected.
   - Conversely, every expected name must occur in that module's `actual`. Thus successful completion implies every expected name exists, is non-private, and has the specified owner. Existence elsewhere does not suffice.
   - Every source public must occur in both arrays. The size check supplies an additional consistency check; membership in both directions, rather than count agreement alone, establishes set equality.

   No prefix, `isInternal`, or exception-list predicate participates in acceptance. The `TCSlib` prefix test later in pass 4 selects modules for the previously closed axiom audit; it is not a surface exemption.

   I compiled the copied surface-check block against isolated imported fixtures. An exact inventory containing an ordinary public name, a public descendant, and an internal-looking public name passed, while a genuinely private helper was excluded. All eight negative cases exited 1: omitted public descendant; omitted internal-looking public; absent expected name; expected name owned by another module; absent source public; mis-owned source public; duplicate expected entry; and an equal-count substitution combining an unlisted actual name with a wrongly owned expected name. The descendant/internal omissions were rejected by the earlier size check; rejection need not reach the final `surfaceBad` diagnostic. These tests address both round-2 counterexample classes without claiming campaign elaboration.

   **Disposition:** Close the outstanding major at the supplied-evidence standard retained from round 2.

2. **[note] All 87 entries are explicitly accounted for, including all seven derived-instance members.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/kernel-surface-inventory.md`; the embedded inventories and source-public arrays.

   I independently parsed every inventory row. Each module's ordered name list equals its embedded array, with no duplicates within or across modules. The source-public rows equal the corresponding `publics*` arrays name-for-name. Every one of the 27 source-public auxiliary rows identifies a generating declaration present in that module's source-public list.

   | Owned module | Source publics | Their auxiliaries | Imported-definition equations | Private-type derived family | Total |
   |---|---:|---:|---:|---:|---:|
   | Nondeterminism | 8 | 3 | 4 | 0 | 15 |
   | EXP | 8 | 13 | 1 | 0 | 22 |
   | SAT | 5 | 0 | 3 | 7 | 15 |
   | Snapshot | 14 | 10 | 0 | 0 | 24 |
   | Tautology | 5 | 1 | 0 | 0 | 6 |
   | Hardness | 5 | 0 | 0 | 0 | 5 |
   | **Total** | **45** | **27** | **8** | **7** | **87** |

   The imported-definition bindings are explicit: Nondeterminism owns the three `Turing.NDTM.runWith` equation lemmas and `Turing.NDTM.stepWith.eq_1`; EXP owns `Turing.solveSplitWith.eq_1`; SAT owns the `Std.Sat.CNF.WidthAtMost`, `fallback`, and `numVars` equation lemmas. Their generating definitions and source locations are identified separately from their kernel owning modules.

   The SAT family consists of `Complexity.instDecidableEqSatStreamState`, its `.decEq`, `.decEq.match_1`, and `.decEq._proof_1` through `.decEq._proof_4`: **1 + 1 + 1 + 4 = 7**. Every member is explicitly inventoried under SAT and bound by the review to `SatStreamState`'s `deriving DecidableEq`. None relies on an internal-name exemption. The corrected total is **45 + 27 + 8 + 7 = 87**, also **15 + 22 + 15 + 24 + 6 + 5 = 87**.

   These are exact checks of the supplied review's names, classes, and generator associations. The campaign-specific generation provenance remains supplied review evidence, not something the checker proves merely from a name's spelling. The descriptive qualifications below do not change these memberships or generator bindings.

3. **[minor; open] A private type does not justify calling its public derived-instance family “unusable downstream.”**

   **File/declarations:** `kernel-surface-inventory.md`, all seven `instDecidableEqSatStreamState` rows.

   The categorical rationale is incorrect for the Lean 4.25.0 legacy-import setting tested here. A consumer can use the public constant while inference supplies the private type. In an isolated producer I declared a private structure `SurfaceDerived.Hidden` with `Nat` and `Bool` fields and `deriving DecidableEq`. A separate importing consumer successfully compiled:

   ```lean
   def downstream := SurfaceDerived.instDecidableEqHidden
   def EqCarrier {α : Type} (_ : DecidableEq α) : Type := α
   abbrev Recovered := EqCarrier SurfaceDerived.instDecidableEqHidden
   def compareRecovered (x y : Recovered) : Decidable (x = y) :=
     SurfaceDerived.instDecidableEqHidden x y
   ```

   The consumer also successfully aliased the generated `.decEq._proof_1`. Its corrected final run exited 0. Ordinary record construction was separately rejected because the constructor is private; that narrower restriction does not prevent the successful uses above. This is a counterexample to the inventory's stated rationale, not a claim to have compiled a consumer of the unavailable campaign artifacts.

   **Proposed resolution:** Append a correction saying that these are non-private generated constants whose types mention a private structure; do not claim downstream unusability. Preserve all seven in the surface inventory. This is a documentation defect, not a remaining surface-coverage major: the repaired checker already counts and checks the entire family.

4. **[note] Two harmless descriptive remnants should be recorded accurately.**

   `R3Axioms.lean` still defines the old 11-entry `generatedExceptions` array. I found exactly one identifier occurrence: its definition. It is unused by the checker. Therefore the repair has **no exception-based acceptance**, but the pack/resolutions' literal claim of “no exceptions array” is inaccurate. Retire the dead array or clarify the wording in a subsequent record; leave the immutable pack unchanged.

   The inventory groups `Complexity.enumWord._unsafe_rec` with structural-recursion unfolding auxiliaries. More precisely, Lean 4.25.0's `Lean.Elab.addAndCompilePartialRec` creates the partial-recursive implementation companion with that suffix; `_sunfold` is the smart-unfolding auxiliary. The generator association to `enumWord` and the broad generated-auxiliary class remain correct. This terminology refinement creates no additional surface defect.

5. **[note] Execution and snapshot claims retain the round-2 evidence boundary.**

   The supplied log contains all six success rows and ends with `R3 CLOSURE AUDIT PASS`. Its reported owned-module totals sum to **820 + 490 + 786 + 41 + 439 + 1550 = 4126**; its whole-import total remains 11,510. These are consistent maintainer run records. The resolutions assert exit 0 and source-hash equality with the pinned round-2 manifest. This five-attachment bundle does not supply the complete campaign sources/oleans or a new hash-assertion transcript, so I did not independently reproduce that run or rehash those sources. This preserves the previously accepted qualification rather than reopening a frozen requirement.

   My independent work was bundle hashing/counting, complete inventory/list comparison, checker inspection, and isolated Lean probes. The probes used Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, on Linux x86-64. The binary required an auditor-local, per-command `LD_PRELOAD` shim redirecting only `/proc/<current-pid>/exe` to `/proc/self/exe` to locate its installation; no proof-checking code was modified. The shim source SHA-256 is `0ca4fb9462e69e7ab3921d9e4af309b7784403353063be1a25acc3d0587a0b6c`. I consulted no campaign repository history and changed no supplied artifact.

Glossary of probe notation: `SurfaceDerived.Hidden` is the private test structure; `α` is the type parameter recovered from an equality-decision instance; `EqCarrier` performs that recovery; `Recovered` names the resulting type; `downstream` and `compareRecovered` are consumer definitions using the public instance. Other code identifiers retain their supplied meanings.
