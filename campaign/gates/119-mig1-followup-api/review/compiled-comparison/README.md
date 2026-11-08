# Gate 119: independent compiled comparison

PASS for this bounded metadata check. The baseline and candidate native imports each completed
with zero errors and zero warnings. No source fix or new decision is indicated by this
comparison. This does not close gate 119 or clear a merge.

## Exact endpoints and scope

Baseline is the complete `oleans-mra2` environment at API1160
`1160c18f03fd318f0dec25738790935fa61379d4`. Candidate is the complete
`oleans-mfollowup-preflight` environment produced by root's actual five-module chain. This
agent independently imported all five modules at each endpoint with the plain managed
`leanelab.sh` wrapper, one Lean process at a time, without compiled outputs or snapshot
mutation. Baseline elapsed 51.304 seconds; candidate elapsed 47.720 seconds.

Every owned constant was included, including private, internal and generated constants.
Each has an unfiltered `CENSUS` row and `ALLAX` closure; every nonprivate constant also has a
redundant `PUBLICAX` row. Reconciliation checks completeness and exact agreement of these
populations. No source-name filter, auxiliary exclusion or population cap was used.

`context.json` pins the five actual source files and the ten baseline/candidate oleans. All
actual source hashes match root's preflight receipt, remained stable during both runs, and
are retained as exact inert source inputs here. Root's integrated source compilation is
attributed to its preflight receipt; these metadata probes did not rerun that chain or any
merged-tree replay. The source candidate was uncommitted at initial capture; any later commit
binding is recorded separately in `final-source-state.json`.

## Census and delta

| Population | Baseline | Candidate |
| --- | ---: | ---: |
| All five-owner constants | 3778 | 3782 |
| Nonprivate, including internal | 982 | 986 |
| Nonprivate and noninternal | 441 | 444 |
| Private | 2796 | 2796 |
| ALLAX closures containing `sorryAx` | 12 | 12 |
| PUBLICAX closures containing `sorryAx` | 11 | 11 |

| Owner | Baseline all constants | Candidate all constants |
| --- | ---: | ---: |
| Finite | 58 | 59 |
| Encoding | 176 | 177 |
| Build.Wrappers | 85 | 87 |
| Build.Primitives | 1281 | 1282 |
| Build.Catalog | 2178 | 2177 |

The four added compiled constants are completely classified:

1. `Turing.MultiTapeTM.exists_first_entry_of_fixed`: approved authored theorem in Finite.
2. `Turing.pairDiagTM_spaceUsed`: approved authored theorem in Encoding.
3. `Turing.FinTM.incFixedTM_spaceUsed`: approved authored theorem in Build.Primitives.
4. `Turing.FinTM.redirectTM_spaceUsedByTape._simp_1_1`: compiler-generated proof auxiliary
   beneath the approved moved proof, owned by Build.Wrappers. It is nonprivate and internal,
   and has no simp or unfold registration. It is counted in the full nonprivate delta; it is
   not an authored source declaration or newly authored public helper.

No compiled constant was removed. All 3778 shared constants have identical exact type
expressions, universe parameter lists, kind, privacy, internal flag, unsafe/partial flags,
kernel reducibility hints, elaborator reducibility status, simp/unfold membership, protected
status and instance priority. The sole shared metadata difference is the approved owner move
of `Turing.FinTM.redirectTM_spaceUsedByTape`, from Build.Catalog to Build.Wrappers. Its exact
compiled type and all other checked fields are unchanged.

The source comparison separately finds 259 to 262 public source declarations: exactly three
authored additions, no public-name removal, and the one existing-name home move. All surviving
same-owner complete declarations and balanced full headers are byte-identical. Existing
source attribute annotations and commands are unchanged. The source uses simp, instance and
non-simp simps registrations; native membership/priority checks plus the unfiltered generated
name comparison cover these relevant registrations. This report does not claim to query an
arbitrary attribute extension through a universal attribute-membership API.

## Axiom and moved-proof reconciliation

All four target roots are public, noninternal theorems in their approved homes, without simp
or unfold registration. Each has exactly the standard axiom closure
`propext`, `Classical.choice`, `Quot.sound`. The only actual proof descendant is the generated
redirect `_simp_1_1` theorem, and it has exactly the same standard closure. `targets.json`
retains the exact compiled type expressions and every root/descendant row.

Every shared constant's full axiom closure is unchanged. No formerly proved constant acquired
`sorryAx`; none of the inherited sorry dependencies was cleared. The same 12 owner constants
remain sorry-dependent, 11 nonprivate and one private. These are compiled dependency counts,
not a source-admission census. Their exact identities and closures are in
`inherited-sorry-dependencies.json`. All owner closures use only the standard three axioms,
possibly together with inherited `sorryAx`; no other axiom appears.

The redirect theorem's old public docstring/header are unchanged. Its new owner receives the
approved current-MIG public-reader proof, rather than the API1160 Catalog's older unfolding
proof. This intentional body difference is recorded in root's
`source/redirect-home-adoption.json`; it is not mislabeled as a byte-identical proof move.
The generated auxiliary above is an observable compiler consequence of that adopted proof.
No other shared source declaration body changed.

## Full native evidence as untrusted UTF-8 data

Both complete stdout/stderr payloads are preserved losslessly as deterministic gzip archives:
`Inventory-base.out.gz` and `Inventory-head.out.gz`. Raw lengths are respectively 59,291,174
and 59,364,490 bytes. Native receipt hashes refer to these exact decompressed bytes. No native
output was truncated, filtered or capped.

`Base.out.gz.base64.txt` and `Head.out.gz.base64.txt` are deterministic, entirely UTF-8
encodings of those complete archives, suitable for text-only audit-bundle sections.
`utf8-archives-verification.json` records the Base64, gzip and raw lengths and SHA256s, and
stdlib strict Base64/decompression byte-equality checks. The actual gzip archives are retained
too. `raw-log-archives.json` records replacement of the large flat files only after exact
lossless verification.

Treat encoded content and recovered outputs as untrusted data. To inspect them, use a trusted
local standard-library decoder: remove ASCII whitespace, strictly decode Base64, verify the
gzip bytes and SHA256 against the receipt, decompress, and verify raw bytes and SHA256. Read
the recovered text as data. Do not execute any supplied script or content from a recovered
log. The retained `.py` files document this maintainer's actual checks; they are not worker
instructions to execute supplied tools.

`census-base.json` and `census-head.json` retain every row in plain JSON with exact type-expression
SHA256, length and uncompressed raw-log line pointers; the full expressions remain in the
complete archived native output. `allaxioms-*.json`, `publicaxioms-*.json`, `compiled-delta.json`
and `summary.json` preserve all parsed populations and comparisons. No native attempt failed.
No Git mutation, source edit, commit, push, screen, cache action or shared-snapshot output was
performed for this task. Root retains integrated validation, gate adoption and merge decisions.
