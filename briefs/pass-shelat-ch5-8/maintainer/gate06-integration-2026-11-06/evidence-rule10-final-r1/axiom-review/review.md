# Gate 06 final axiom census/provenance review

Read-only review at source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, checked ancestor `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
Comparison: initial e9 collector → frozen final collector. This is not a rebuilt PR-base axiom
census, seal pass, external gate approval or merge clearance. No Lean/cache/build or library,
tracked-record, main-evidence or Git mutation was performed.

| Measure | Initial | Fresh |
|---|---:|---:|
| Actual `(module, actual_name)` identities | 2,721 | 2,881 |
| Standard-only axiom sets | 2,675 | 2,835 |
| `sorryAx`-dependent identities | 46 | 46 |
| Unexpected axiom names | 0 | 0 |

There are 2,704 common identities, 177 added to the census and 17 removed: net +160.
Exactly four common sets change; the other 2,700 are equal. All 177 added and all 17 removed
records are standard-only. Of the additions, 158 reflect the three newly collected owner
modules (MultiMessage 64, PolyTimeModel 37, ZeroKnowledge/Encoding 57); 19 arise within the
prior module scope. These are census additions, not 177 new source declarations. The 17
removals are 15 retired Yao private decoder/length-family constants and two generated equations
whose owner definition blocks are unchanged. Exact records and hashes are in the JSON.

| Common identity (namespace shortened) | Axiom-set change | Frozen source explanation |
|---|---|---|
| `Composability.prfFixedScheme._proof_1` | loses `Classical.choice` | `PRFScheme.lean:58–77`: public coin/eval readers, explicit Fin transport, constrained simplification; construction data unchanged |
| `SecureComputation.decodeMsgs_encodeMsgs` | loses `Classical.choice` | `Yao.lean:349–357`: List.rec identifies the public encodings; invokes `decWords_encWords`, retiring private fuel lemmas |
| `SecureComputation.decodeMsgs` | gains only `propext`, `Quot.sound` | `Yao.lean:331`: delegates to the existing well-founded `BinArith.decWords` (`Words.lean:97–100`) |
| `SecureComputation.decodeMsgs_nil` | gains only `propext`, `Quot.sound` | `Yao.lean:360`: public `decWords_nil` replaces the former fuel-decoder `rfl` |

The exact primitive dependency changes are collector observations. The source explanation is
consistent with the revised proof/delegation routes; this review did not regenerate kernel
terms or reconstruct an exhaustive primitive-dependency graph. No changed common set gains
`sorryAx` or a nonstandard axiom.

The **same 46 module+actual-name identities have exactly the same full axiom sets**. Frozen
source inspection classifies them as **33 direct retained statement-phase admissions and
13 proved bodies with transitive admitted dependencies**, with the same classifications at e9.
The JSON lists all 46, source lines/block hashes, and visible dependency routes for the 13.
This agrees with the prior `evidence-rule10-r2/SUMMARY.md:15–21` disposition and both lexical
censuses: library 511 → 544, prong admissions 0 → 33, no outside-prong sorry-count change;
zero `admit`/`axiom` commands on both comparison sides. The standard-only quantitative 3COL
negligibility estimate does not make its repetition corollary or abort/perfect repetition
standard-only. Unchanged status does not waive or fill any admission.

Both complete raw logs were independently reparsed for multiline AXIOMSID lists and compared
as multisets to the canonical JSON; AXIOMS display rows agree as alternate renderings. No
actual-identity duplicate was silently dropped. Display names are not identity keys (fresh:
142 rows display differently from their actual spelling). Initial/fresh collectors both report
rc0 and zero error diagnostics. Anonymous-command/seal/control coverage remains a separate
check; this census alone does not certify it.

Inputs: initial JSON SHA `a292ed402dfedcdd9abdf784ffcbb7b4fc886e7d2239d38cb3ced40c843f69c8`;
fresh JSON SHA `81441d20992a14945e7fc8815118e667f1ce7a8e70f6cc4044e2ecfe693dd13d`.
Full input/log/source pins are in `review.json`.
Review JSON SHA-256: `5897ad171a0ad1af2b7c8479de557e93766f053d0892d38d97452d72d79f8438`.

**Not yet clear to merge — this is an axiom/provenance record only; final seal/failure dispositions and external gates remain separate.**
