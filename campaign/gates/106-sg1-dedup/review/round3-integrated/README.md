# Final combined SG1 validation

**Not yet clear to merge** — #215. The exact final SAT → Hardness two-module compile and compiled metadata pass. This is not the current campaign merged-tree replay or gate closure.

Execution began with the previously verified detached `478cd3a8dfb46094b9d8b971662f2ddadb1eccdb` worktree and uncommitted repair bytes. The earlier read-only HEAD receipt is in `../round3-closure-repairs/context.json`; the supplied base is also recorded in `../round3-prefix-repair/context.json`. Subsequent parent commits do not relabel these executions. Inputs are MSG4's complete **pre-#230 dependency context**, with these exact two sources:

| Source | SHA-256 | Compile | Warnings |
|---|---|---:|---:|
| SAT | `682df0cd83abed16dac1e44768bee40a1691030eaeab1cf56373fa0677dbc6ba` | PASS, 19.46 s | 83 |
| Hardness | `a6edf9fe11e89d71a028143d1cedf9be896124bbcbc5a86d779e6c6278b5c597` | PASS, 162.89 s | 66 |

Both full sources are archived verbatim as inert `.lean.txt`. Hardness compiled against the freshly produced SAT output in the **same** complete overlay. Both actual source hashes were checked before/after compilation and again at freeze. No source was edited by this task.

The APFS clone contains all 895 baseline entries (1,292,002,328 regular bytes before mutation), verified individually before compiling. Each target output was unlinked before replacement. Final checks confirm the shared MSG4 snapshot is byte-identical to its original inventory, all 895 overlay paths remain present, and the other 893 entries are unchanged. Only `SAT.olean` and `Hardness.olean` differ. The reusable private overlay is `/private/tmp/tcslib-g106-r3-integrated-4trrpdy7/overlay`; its full final inventory and the nine owner-module artifact pins are retained here.

## Compiled proofs and original population

`combined16.json` is the complete requested repair list, with source names and module owners. `repair-roots.json` records all exact compiled private names and descendants without normalizing private IDs:

- SAT: `sat_pt_mapSnd`, `sat_pt_pair`, `sat_pt_append`, `sat_pt_pair_input`, `sat_pt_unaryLength`.
- Hardness: `clNative_map`, `clNative_pair`, `clNative_append`, `clNative_unary`, `clNative_linear`, `clA5_pt_const`, `clA5_pt_cond`, `clA5_pt_and`, `clA5Pair_sizes`, `clA5Le_native`, `clA5Drop_native`.

All **16 roots plus seven generated descendants** have only standard axioms (`propext`, `Classical.choice`, `Quot.sound`, or subsets), with no `sorryAx`. The selected roots are private theorems. Descendant enumeration includes matcher definitions, their serialized equations/splitter, and the two `clA5Pair_sizes` proof auxiliaries. The selected AX results agree across both independent metadata probes.

The original nine owners are listed in `original9-owners.txt`. Their complete compiler census contains **7,063 constants: 5,714 private and 1,349 nonprivate**. `ALLAX` covers exactly those 7,063 names, and `PUBLICAX` exactly their 1,349 nonprivate names. These are compiler counts, including generated constants, rather than source export counts. Per-owner/kind/privacy totals and complete name maps are in `metadata-summary.json` and `compiled-census.json`.

Nine unchanged inherited constants have `sorryAx`, all owned by the old MSG4 Primitives artifact: eight nonprivate results (`appendBitTM_computes`, `polyBitsTM_computes`, `polyUnaryTM_spaceUsed`, `splitSolveTM_computes`, `splitSolveTM_spaceUsed`, `splitSolveWithTM_computes`, `stripLastTM_computes`, `unaryTokenTM_computes`) and private `split_fuel`. Exact names/axes are in `compiled-whole9-nonstandard-axioms.json`. These results must not be substituted for post-#230 compiled totals.

The direct selected-proof inventory contains 72 TCSlib citations and no private reference from a different module home. Eight same-home private references (local header readers, matchers, and proof auxiliaries) are classified separately. The retained ordinary-definition inventory includes public model/pair/prefix interfaces; this metadata check adds **no new opacity seal claim**. CITED inspects direct types/values; axiom collection is transitive. The kernel environment is used for constant lookup, retaining serialized generated descendants rather than filtering them.

## Separate opacity and import evidence

The prior three frozen evidence manifests and every listed payload were rehashed successfully; exact manifest pins and control results are in `final-artifact-verification.json`:

| Prior folder | Scope | Effective point/abstract controls |
|---|---|---:|
| `round3-closure-repairs` | Original 13 proof-section repairs | 36 |
| `round3-extra-repairs` | Pair sizes and native length comparison | 40 |
| `round3-prefix-repair` | Approved Prefix import and Drop repoint | 42 |

Those are separately pinned native/scoped-seal results, not a claim that all legacy source was sealed in this task. The prefix folder records the approved one-import closure change: 45 → 51 TCSlib source modules (six additions), and 2,732 → 2,738 total source modules. Its exact closure/source pins remain separate and immutable.

All four Lean invocations here passed with zero errors: full SAT, full Hardness, selected-root/census metadata (12.48 s), whole-nine AX metadata (116.78 s). Exact commands, raw outputs, runners, parsing/verification code and receipts are retained. Local wrapper budget was three under the machine budget five; only one own Lean invocation ran at a time. No screen, Git mutation, shared snapshot/cache write, or new source edit occurred. The current merged-tree replay and external gate remain parent/user work.
