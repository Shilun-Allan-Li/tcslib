# Chapter-7 fill-campaign drift attestation

Baseline: the ch7-phase1 gate-audited surface, commit `76fe2f46` (the pack/bundle
commit; the post-gate minor/note sweeps at `c4114867` were comment-only and vanish
under comment stripping). Current: the campaign head carrying the completed fill
(`d450376` plus this closure commit, which also carries the closure documentation
sweep — 31 comment-only docstring/sketch additions across nine audited modules,
each mechanically verified comment-only and therefore invisible to the comparison
below). Method per `workflow.md` §6: strip comments
from every module, compare the ordered declaration sequence and multiset against
the baseline, and enumerate public declarations gained / lost / signature-changed.
Signature comparison splits each declaration at its first top-level `:=`
(whitespace-normalized), so a filled proof body never masks a statement change.

## The 13-module audited surface

| Module | decls (base → now) | result |
|---|---:|---|
| `Expanders/Basic` | 17 | comment-stripped **identical** |
| `Expanders/Mixing` | 2 | comment-stripped **identical** |
| `Expanders/Walks` | 17 | comment-stripped **identical** |
| `Expanders/Chernoff` | 1 | comment-stripped **identical** (Thm 7.41 stub untouched) |
| `Randomized/SchwartzZippel` | 1 | comment-stripped **identical** |
| `Randomized/ErrorReduction` | 13 | comment-stripped **identical** |
| `Randomized/Classes` | 50 | comment-stripped **identical** (gate's minor sweep was comment-only) |
| `Randomized/Adleman` | 2 | comment-stripped **identical** |
| `Randomized/SipserGacs` | 13 | comment-stripped **identical** (gate's note sweep was comment-only) |
| `TuringMachine/CounterProgInput` | 5 | comment-stripped **identical** |
| `CircuitComplexity/PairEncode` | 22 | comment-stripped **identical** |
| `ClassNP/PolyTimePrefix` | 16 | comment-stripped **identical** |
| `Randomized/PolyTimeModel` | 20 → 20 | **same 20 declarations, same order, zero signatures changed, import block byte-identical**; the only comment-stripped difference is the three `sorry` bodies (`closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`) replaced by proofs. The consumed `mem_P_of_block*` lemmas reach the module through its pre-existing `PolyHierarchy/{Padding → Normalize → Collapse}` import chain (`Padding` imports `ClassNP/PClosure`) |

## The frozen Chapter-1/2 file extended by this campaign

| Module | decls (base → now) | result |
|---|---:|---|
| `ClassNP/PClosure` | 13 → 16 | baseline sequence is an **ordered prefix** of the current sequence; gained exactly `mem_P_of_blockAny`, `mem_P_of_blockMajority`, `mem_P_of_blockXorAny` (all public, all proved); **nothing lost, zero signatures changed**; one import added (`ClassNP/PolyTimeBlockMajority`) |

## New trusted surface (no baseline — enumerated for the fill-audit pack)

| Module | decls | public |
|---|---:|---|
| `TuringMachine/Build/EmitIterEmbed` | 18 | 18 (safe runs, output-prefix commutation, padding embedding, control steps) |
| `TuringMachine/Build/EmitIterBody` | 19 | 1 (`FinTM.exists_emitIterTM`; the body machine, copier, and round lemmas are private) |
| `ClassNP/PolyTimeBlockLoop` | 32 | 22 (slices, FP helpers, `polyTimeComputable_emitIter`, `xorD`) |
| `ClassNP/PolyTimeBlockTests` | 25 | 3 (`blockAt`, the OR and XOR-then-OR tests) |
| `ClassNP/PolyTimeBlockMajority` | 14 | 1 (the strict-majority test) |

No other `.lean` file differs from the baseline anywhere in the repository
(`git diff --name-only 76fe2f46..HEAD -- 'TCSlib/*'` lists exactly the modules
tabled above).

**Conclusion.** Nothing audited moved: the phase-1 statement surface is intact
declaration-for-declaration and signature-for-signature; the campaign's additions
are the enumerated new modules and the three additive `PClosure` headliners, all
within the fill-audit pack's scope.
