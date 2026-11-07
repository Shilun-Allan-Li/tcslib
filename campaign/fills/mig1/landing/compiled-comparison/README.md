# Independent compiled-metadata comparison

The supplied logs reconcile exactly. This is a read-only analysis of existing
successful metadata runs, **not** a new Lean run, source acceptance, gate closure,
or merged-tree replay.

| Eleven-owner census | Total | Private | Non-private |
| --- | ---: | ---: | ---: |
| API prerequisite baseline | 5,656 | 4,400 | 1,256 |
| Landing current1 | 4,370 | 3,163 | 1,207 |
| Landing final2 | 4,372 | 3,163 | 1,209 |

Baseline→final2 has **398 exact-name additions** (266 private, 132 non-private),
**1,682 removals** (1,503 private, 179 non-private), and **3,974 names in both**.
For those shared names, recorded owner, kind, privacy and internal-detail flags
do not change. This compares printed names and attributes; it does not assert
unchanged proof bodies, types, or semantic identity across private-name churn.

## Non-private compiler constants versus source exports

| Classification of changed non-private names | Added | Removed |
| --- | ---: | ---: |
| Source-declared exports | 3 | 6 |
| Deriving-instance family and its generated artifacts | 71 | 71 |
| Proof, matcher and equation auxiliaries | 56 | 101 |
| Generated foreign-home equation theorems | 2 | 0 |
| Generated foreign-home congruence theorem | 0 | 1 |
| **Total** | **132** | **179** |

Thus the non-private net **−47** is the source-export net **−3**, plus generated
artifacts net **−44**. The three added source exports are `pairMapSndTM`,
`pairMapSndTM_computes`, and `pairMapSndTM_spaceUsed`, in Primitives. The six
retirements are Catalog's `transferTM_run`, `copyTM_run`, `clearTM_run`,
`compareTM_run`, `incrementTM_run_succ`, and `incrementTM_run_overflow`.

The 71-name deriving family changes from Catalog's
`instDecidableEqA2_MapState` family to Primitives' `instDecidableEqFwdMapState`
family. Both underlying state types are written `private inductive … deriving
DecidableEq` (baseline Catalog:5479; final Primitives:2680). In each family the
instance and `decEq` definition have `internal=false`, despite being generated;
its 69 further artifacts have `internal=true`. The other removed generated
name with `internal=false` is `Fin.castLEEmb.congr_simp`, emitted in baseline
CodeSimulator. Therefore `private=false` and `internal=false` together still do
not identify an explicitly written source export.

The lexical source-name comparison independently confirms +3/−6. Its totals
(364→361) count written top-level declarations under the repository's
`declfreeze` rules, not every generated or approved API name: for example,
published field readers produced by `simps` are not written declaration roots.
Generated status alone neither approves nor rejects an interface.

## Current1→final2 and the two extra non-private names

Current2 adds 12 names and removes 10, all within Primitives. Private additions
and removals are ten each. The only non-private additions are:

- `Turing.solveSplit.eq_def`
- `Turing.solveSplitWith.eq_def`

Both are generated theorems with `internal=false`, attributed to Primitives by
the compiler metadata. The functions themselves are defined in Convention
(lines138/227). The final Primitives source explicitly rewrites with those
generated equations at **4013** (`splitFind_eq`) and **5576**
(`emitterSplit_find`). They explain the two-count increase; they are not two
additional source export declarations. Their foreign generated-reader use has
been flagged to the maintainer for separate source/rule-10 disposition. This
comparison does not infer API approval from successful compilation or axioms.

Module ownership here means the module reported by `getModuleIdxFor?`; generated
code can be materialized in a consumer module. A name absent from this
eleven-owner population is not, by that fact alone, proven absent from the whole
imported environment. These observations are scoped compiler metadata, not a
claim about when an on-demand equation becomes globally available.

## Axioms and pending APIs

Final2 has **ALLAX for every one of its 4,372 constants**, matching CENSUS names
exactly. All except the following three depend only on a subset of
`[propext, Classical.choice, Quot.sound]`:

- `WordRAM.wordSizeComputable_of_spaceConstructible`
- `WordRAM.wordSizeComputable_logSpace`
- `WordRAM.WordSizeComputable.mono`

These three WordSize theorems retain `sorryAx` in their dependency sets. All
**93 selected roots** have standard sets: 78 use standard3, ten use
`[propext, Quot.sound]`, and five use no axioms. Their population equals the 88
requested named roots plus the five selected private roots, independently
checked against the supplied probe text.

Both endpoints provide PUBLICAX. Among common non-private names, 23 axiom sets
change: **22 lose `sorryAx`**, and one polynomial-row generated proof auxiliary
loses `Classical.choice` while remaining standard. The baseline has 25
sorry-bearing non-private names; final2 has the three RAM names. These are
dependency-bearing constant counts, **not counts of direct admissions**.
Baseline/current1 do not contain ALLAX, so no baseline-private axiom comparison
is claimed.

All three explicitly tested pending APIs remain absent in every supplied probe:
`pairDiagTM_spaceUsed`, `FinTM.incFixedTM_spaceUsed`, and
`MultiTapeTM.exists_first_entry_of_fixed`. This uses the probes' actual
`env.contains` tests and PASS receipts, not merely absence from the owner census.

## Per-owner counts

| Owner suffix | Baseline total | Final2 total | Baseline non-private | Final2 non-private |
| --- | ---: | ---: | ---: | ---: |
| TimeConstructible | 86 | 99 | 11 | 16 |
| WordSize | 4 | 4 | 4 | 4 |
| Catalog | 2,178 | 663 | 626 | 485 |
| CertShell | 93 | 96 | 15 | 15 |
| Loop | 604 | 618 | 45 | 47 |
| Primitives | 1,281 | 1,462 | 136 | 231 |
| Wrappers | 85 | 107 | 35 | 35 |
| CodeSimulator | 886 | 886 | 43 | 42 |
| Composition | 88 | 84 | 48 | 43 |
| Encoding | 176 | 176 | 130 | 130 |
| Simulation | 175 | 177 | 163 | 161 |

The complete owner/kind/privacy/internal-detail distributions are in
`summary.json` and the delta JSONs. Baseline→final2 kinds are: theorems
4,610→3,542, definitions 956→757, constructors 62→49, inductives 14→12 and
recursors 14→12. No exact shared name changes kind.

## Receipts, reproducibility and limits

Raw inputs, their probes and PASS receipts are copied verbatim. SHA-256 values:

| Output | SHA-256 |
| --- | --- |
| Baseline | `f93297583f66c824e2166fda5898e1bf85af04331362ca3d9a2d719680526498` |
| Current1 | `d53641f8834215f228f97873e9a1c36490beb788ff65cd481cf23f3637fa63b1` |
| Final2 | `3a3951e60053f335ffdfc081d7277ecfd39b3fb8bfb434afa64b871cb6d44740` |

`inputs.json` verifies output and probe hashes against each existing run receipt.
Final source classification uses the exact archived compile inputs, including
Primitives `483ab96b55b400c3c1d4df9796b38cfec20b09f0360c68fe97a560212b1d0b80`
and CodeSimulator
`57e7dc52dedf3d146499ad5694270d1c6fee7255cad74338d4174c5cce3e1a73`.
Baseline source names were read from the supplied frozen API worktree; no new
Git or source-to-olean attestation was run here.

Run `python3 -I …/compiled-comparison/parse.py` to reproduce. It strictly checks
tag shapes, duplicates, wrapped axiom lists, complete axiom coverage, selected
roots, absent-API markers and receipt hashes. The retained trusted lexical
helper is pinned by SHA-256 and used as parser code; no incoming or metadata probe script is
executed. The first parser attempt incorrectly equated Lean's `Name.lt` order
with Python string sorting; that failed attempt is preserved, and only its
ordering assertion was removed. Raw axiom lists remain verbatim in meaning.

`map-*.json` retain every census/axiom/root/citation record and raw line number.
`delta-*.json` retain every addition/removal, shared name, changed axiom set and
same-root direct-citation delta. CITED lists are **direct** type/value references,
not a transitive dependency closure; baseline selected only two roots, so
all-edge count differences would confound selection with proof changes.
Private IDs are never normalized or assumed stable, and no cross-name
semantic move, rename or privacy change is inferred. No Lean, screen, source,
Git, cache, snapshot, commit or push action was performed for this comparison.
