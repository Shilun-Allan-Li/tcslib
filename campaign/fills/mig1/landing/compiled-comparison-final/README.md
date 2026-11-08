# Final compiled metadata: independent crosscheck

The final twelve-owner metadata reconciles exactly. This checks the supplied native PASS outputs
for final source `b1f553b315f31b949076e91119473ce4070e7d53`, plus two specifically authorized small
equation-inspection runs. It is **not gate clearance or a new merged-tree replay**.

| Twelve-owner census | Total | Private | Non-private |
|---|---:|---:|---:|
| API prerequisite / mra2 | 5698 | 4405 | 1293 |
| Final / current4 | 4413 | 3170 | 1243 |

Exact-name delta: **398 additions** (269 private, 129 non-private), **1683 removals** (1504 private,
179 non-private), **4015 shared names**. Private IDs are preserved literally; no normalization or
cross-name semantic matching is performed. Shared names alone do not prove equal types or bodies.

## Authored declarations versus compiled constants

| Changed non-private constant class | Added | Removed |
|---|---:|---:|
| Written top-level source exports | 3 | 6 |
| Deriving-instance family and generated descendants | 71 | 71 |
| Proof/matcher/equation auxiliaries | 53 | 101 |
| Foreign-home reserved `.eq_def` materializations | 2 | 0 |
| Foreign-home generated congruence theorem | 0 | 1 |
| **Total** | **129** | **179** |

Thus compiled non-private net **−50** is authored source-export net **−3**, plus generated net
**−47**. The authored additions are Primitives' `pairMapSndTM`, `_computes`, `_spaceUsed`; the six
retirements are Catalog's `transferTM_run`, `copyTM_run`, `clearTM_run`, `compareTM_run`, and the
success/overflow `incrementTM_run` rows. Immutable final QA sources independently give source
public **384→381**, private **1080→766**: 65 added source declarations (62 private), 382 removed
(376 private). These are source-declaration counts, not compiled-constant or direct-admission counts.

The deriving family changes from `instDecidableEqA2_MapState` to `instDecidableEqFwdMapState`.
Its instance and `.decEq` are non-internal public `def`s despite deriving from a private type;
their 69 generated descendants complete each 71-name family. `private=false/internal=false`
therefore does not identify an authored source export. The two `.eq_def` names are
`Turing.solveSplit.eq_def` and `Turing.solveSplitWith.eq_def`, materialized in Primitives and
explicitly used at final source lines 4075/5638. Their reserved-reader/source disposition is
separate from this accounting. The removed congruence theorem is `Fin.castLEEmb.congr_simp`.

The final census includes private `loop_computes_of_startup`, `emCall_bank_embed` and
`bufferReplay_run`; old `catalogRewind` is present only in the baseline. The short-lived
`emCall_pair_not_mem` and `emCall_triple_not_mem` are absent at **both** endpoints, having been
pruned before final metadata; they must not be invented as baseline→final removals. Complete
exact-name/helper maps and source deltas are retained.

## One shared generated-owner change, formula checked

Only **`Turing.splitAtLastTrue.eq_1`** changes a recorded shared attribute: owner **Catalog →
Primitives**. It remains a non-private, internal theorem. This is compiler materialization
ownership, not an authored definition move or home approval.

Parent authorized exactly two small managed probes in the same twelve-import contexts. Both
passed with 0 errors/warnings (1.79/1.76 s). For the **actual function and actual eq_1**, their raw
type and value `repr`s are **byte-identical across contexts**, including binder/hygiene IDs;
no normalization was used. Both have `AX=[]`, `simp=false`, `unfold=false`. The function's owner
stays Convention. The equation has the same defining formula:

```lean
splitAtLastTrue v =
  match v.reverse.dropWhile (fun b => !b) with
  | true :: rest => some rest.reverse
  | _ => none
```

The entire Convention source is identical, SHA-256
`7de288c338b6f6a2a5d90b5258f552049feb28929e15842b2bde93b825ce183f`.
Its binary `.olean`s differ, so binary equality was **not** assumed; an initial setup assertion
detected that and its context record is retained. The direct expression comparison passed.
`equation-comparison.json` retains complete raw forms, formula and attributes. Referenced
constants were not recursively compared. This shared equation is distinct from the two added
reserved `.eq_def` materializations above; none of these observations grants API/home approval.

## Axiom, root and citation coverage

Both endpoints have **ALLAX names exactly equal to CENSUS** (5698/4413), and PUBLICAX names
exactly equal to the non-private subset (1293/1243), with agreeing sets and no duplicate records.
Only these three final owned constants have nonstandard axioms, all retaining `sorryAx`:

- `WordRAM.WordSizeComputable.mono`
- `WordRAM.wordSizeComputable_logSpace`
- `WordRAM.wordSizeComputable_of_spaceConstructible`

The final **144 source roots** (66 public/78 private) match the source QA, probe request list,
native ROOTMAP, owners, privacy and compiled theorem kinds exactly. Their **224 descendants**
are exactly the full prefix-name populations in CENSUS: **368 selected constants**, all standard.
The axiom distribution is standard3 **201**, `{propext,Quot.sound}` **148**, `{propext}` **14**,
empty **5**. ROOT-only distribution is standard3 140 and `{propext,Quot.sound}` 4.

Across shared exact names, 31 axiom sets change (23 non-private/8 private); **23 lose `sorryAx`**
(22 non-private and private Primitives `split_fuel`). None gains it. Baseline's 26 nonstandard
dependency-bearing names are not a count of direct source admissions.

All **5434 CITED records** are retained, separated by root, descendant and **type (1670) / value
(3764)**. Their 20 TCSlib owners are all covered by the QA's proposed 25-file population. This
does not attest a screen or final bundle. CITED is direct constant use, not transitive dependency
closure or a Rule-10 seal. The three explicit native `env.contains` absence tests pass at both
endpoints: `pairDiagTM_spaceUsed`, `FinTM.incFixedTM_spaceUsed`, and
`MultiTapeTM.exists_first_entry_of_fixed`.

Previous phase2→final has the same 4413 names, attributes, ALLAX sets, selected populations and
direct CITED sets. The third tagged-run proof **did change**; this equality illustrates why these
metadata fields cannot certify identical proof bodies.

## Evidence and limits

Base output/receipt is a byte-identical reuse of the prior same-twelve-owner mra2 native run.
Final Head is the supplied native current4 run. Raw input/output hashes and PASS receipts match;
final archived source hashes match every source pin in the provided pushed-head receipt. This
review did not run Git, independently verify that commit object, repeat either full census,
replay sources to oleans, alter source/cache/snapshot, run a screen, commit or push. Only the two
explicitly authorized small equation probes invoked Lean, through plain managed wrappers at
local budget three. No control/proof consumer or new API was implemented.

`parse.py`, `compare-equation.py` and `finalize-data.py` retain the parsing/checking logic.
Complete maps, deltas, classifications, raw logs, receipts and source pins are included. Census
membership is restricted to twelve owners; disappearance from it is not a whole-environment
absence claim. No new public-interface or debt decision follows from this crosscheck.
