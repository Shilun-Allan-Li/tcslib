# Cleanup PFR route — independent static review r1

Verdict: **0 blockers, 0 majors, 0 minors in the final reviewed five-file route.** The concrete guarded route is suitable for issue after final external checksum/path bindings and an explicit maintainer native status. It is not a native bootstrap, object-identity or cleanup acceptance result.

## Scope and identity

Read all three authored Python sources, RUNBOOK.md and PFRIdentityProbe.source.txt as data. Independently checked the unchanged checker and relevant installed Lean 4.25.0 primary sources. No supplied tool was imported or executed; no Lean/Lake/cache/build/app command or Git mutation was run. An independently authored read-only Git/text validator was executed with python3 -I; it is supplied beside this review.

The cleanup source ancestor is `1aa5506f58f77c215e56d24311ec33bd931cacf1`. The frozen external supplement is `70dd1a408a2c0c46af7ab2da50ff50520b26b2983e298492935008debb1a2cbd`; the original 45 inputs remain governed by the prior final-review-r1 validation. This review adds no mathematical scope or public exception.

| Reviewed file | Bytes | SHA-256 |
|---|---:|---|
| `prepare_pfr.py` | 5702 | `52b83d8e2dd73ab7a70cf7d66e5d4da439fb77e1417e3ba2fd09b9618b48110e` |
| `pfr_lean.py` | 2404 | `41fda9565be3f77462fe6f2f7b55b798c5bf34fbbc400a648f77e000eb36636d` |
| `native_validation.py` | 10664 | `59477e2ed3786b48c60ac2342b1613a8a403209966b3d7e1d603327b3b10f1b8` |
| `RUNBOOK.md` | 7368 | `4102e174171f787bbc56ec497140b6a3272937ff1fc0ad23a25f5c2783fc6f55` |
| `PFRIdentityProbe.source.txt` | 2918 | `8b539d107e9ac09cb86825f1411e8942dd8e0386ff4d2bfc6353f74d379ae575` |

The unchanged `scripts/lean_check_tree.sh` SHA-256 is `366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335`. The latest runner includes the small fallback-regex correction for literal `download(s) failed`. Superseded source fingerprints from the preliminary messages are not the reviewed final runner identity.

## Independent data checks

All 15 files listed in the frozen external DELIVERY-MANIFEST and all internal manifest outputs match their recorded byte counts and hashes. All 31 unique PFR modules have the correct ordinal and module-to-source path; live source bytes equal their SHA-256, Git blob and exact pinned PFR object at `e1095d58b7c6f10734988816f7764f2103b9bf29`. Independently parsed import names and lines match every row. The order is topological, and the closure of the three designated PFR roots is exactly those 31 modules. There are no LeanAPAP source imports in this closure.

All 30 direct Mathlib boundary source bytes match their exact pinned Git objects. The separate original 375-root list plus 14 additions equals the 389-root union. No bare Mathlib root occurs. The physical checker paths and logical PFR import paths resolve algebraically to the same objects through the single `<tree>/PFR -> .lake/packages/PFR/PFR` namespace alias. These are source/data checks, not filesystem alias creation or object freshness/ABI checks.

The identity template's expected array equals the exact ordered 31-module list. Its three named constants exist at the recorded owner source sites: KLDiv (Kullback:32), ProbabilityTheory.entropy (ForMathlib/Entropy/Basic:45), and ProbabilityTheory.uniformOn_apply_singleton_of_mem (Mathlib/Probability/UniformOn:10).

## Tool and probe assessment

`prepare_pfr.py` requires a fresh runtime; validates present package URL/revision bindings, pinned PFR Git blob identity, source path containment, ordinals/uniqueness, topology, exact package options and source hashes; refuses a conflicting namespace prefix. Its link is an object namespace alias inside the one supplied tree. It neither aliases package source nor fetches, copies, modifies or reclones dependencies. Package absence is recorded, and a required missing source then fails configuration.

`pfr_lean.py` accepts only the unchanged checker's exact `source.lean -o object.olean` argument shape for one of the 31 configured source keys. It rechecks the source, driver, lakefile, toolchain strings, real binary digest, one-tree output and link, then invokes the bound real compiler with the PFR package `--root` and four exact Boolean options. Extra flags/alternate roots and ordinary local sources are rejected. The runbook scopes its PATH assignment to each PFR command and uses ordinary PATH for cache operations and every TCSlib/aggregate/probe check.

Pinned Lean primary source supports this design: Lean/Util/Path.lean:140-153 derives the module name from the real source path relative to the supplied root; Lean/Environment.lean:159-196 documents the module index/header relationship and defines moduleNames; getModuleIdxFor? and getModuleIdx? occur at 1160 and 1175. The constants accessor and imported-map usage support the template's imported constant iteration. AutoBound.lean:17/22 and PrettyPrinter/Delaborator/Options.lean:41/212 register the four Boolean options. This is source-level API validation; it is not Lean elaboration of the template.

The probe checks all 31 imported module headers and all three constant owners under ordinary PATH, rejects any observed private-name prefix inconsistent with its owner, and emits a completion marker. The independent lexical scan found zero explicit private declarations in this 31-file closure. A runtime private count of zero must therefore be reported as zero, with no claim that a nonempty private-name test occurred; generated private constants, if present, are still checked.

The maintainer runner preserves failed logs and nonzero statuses, requires a fresh rN retry directory, separates cache/cache-probe/bootstrap phases and binds the source/tool/checker/static inputs across phases and in FINAL. The checker removes a stale output before invoking Lean and requires a fresh nonempty output. Per-module successful receipts capture source/object and direct-prerequisite source/object hashes. The runner defers on any observed Lean/Lake host process before native phases; the runbook separately requires serial host use. Resource measurements are saved before enforcing disk/memory floors. The macOS proxy is correctly qualified; it is not Linux MemAvailable/cgroup headroom. No dependent check is permitted on a missing or failed prerequisite.

The local maintainer test fetches only the 30 external boundary roots into its existing same-chat tree; the portable worker route explicitly fetches the full narrowed 389-root union in its own clone/tree. The final runner does not claim a full-root/Checks baseline or worker completion. Its per-attempt object checks and owner probe remain required runtime work.

## Earlier findings and candidate wording

The preliminary fixed-label retry problem, lost E-RES measurements and missing runtime input/tool/checker bindings were repaired before this verdict. The fallback regex now also matches the literal parenthesized Cache diagnostic. Pinned Cache/Requests.lean:407-409 independently exits 1 on failed downloads, which the runner rejects.

Candidate r2 fingerprints are recorded in static-validation.json. Its import-direction, Gate06 existing-owner reader exception and explicit attachment-path repairs are present. Its strict PFR-only wrapper rule explicitly supersedes the frozen static README's older pass-through description. No new source/ownership permission is implied.

The r2 native-result table is still intentionally pending. Root has chosen to fill it with actual host deferral/NOT_RUN status rather than imply a native pass. This decision is compatible with the existing issue rules: pre-issue native route testing is recommended here, not a newly imposed cold full-root or human approval requirement. Before issue, replace pending runtime path/hash fields, bind the five exact files and frozen supplement in the issued packet, and state the native limit plainly. Suggested status text:

> Maintainer native PFR bootstrap and owner validation: NOT_RUN (host-busy deferrals; no native bootstrap/owner result). The concrete route and source closure were statically reviewed. At checkpoint 0, the worker must fetch/verify the narrowed cache, run all 31 PFR checks serially in its own clone/tree, then run the ordinary-PATH identity probe. Check dependent modules only after their prerequisites pass. Preserve failures and the blocked frontier, continue only independent authorized work, and make no environment-guarantee or native-owner claim before those checks succeed.

## Evidence limits

The root reported exit-75 host-busy deferrals; this review did not reproduce those executions or independently validate a native receipt. No native tool success, object header, private-name count, PFR proof result, overall source baseline, theorem axiom census or Rule10 clearance is asserted. The worker still has the exact final aggregate/axiom/Rule10 obligations from the issued cleanup brief.

**Not yet clear to merge — static route review is complete; issue bindings/status, worker checkpoint-0 verification and the full cleanup acceptance evidence remain.**
