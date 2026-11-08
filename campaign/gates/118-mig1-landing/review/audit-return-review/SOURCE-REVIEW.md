# Source routes inspected for returned-audit notes118-03–09,11–13

All paths are the exact current source capture under `campaign/fills/mig1/landing/post234-source-QA-final/inputs/head/TCSlib/Complexity/`. The24 BASE/HEAD owner captures were byte-compared to Git source; current owner files are byte-identical atEAecd and55df. Lines refer to those retained `.lean.txt` files.

| Current source | Declarations/routes inspected | Review implication |
|---|---|---|
| TuringMachine/Composition.lean:159,363,793 | idTM_computes, ifEqTM_computes, condTM_computes_iff; run certificates, boundary comparison and startup/branch equivalence | Copy charges final blank. Comparator includes reference-word end test. Conditional extension uses absorbing halt and preserves original input, with both implications intact. |
| TuringMachine/Simulation.lean:431,1093 | branchTM_spaceUsed; generic tagged invariant driver | Idle bank contributes one origin cell per tape at every horizon. The unrestricted driver uses Set.MapsTo.iterate rather than another private iterator. |
| TuringMachine/Encoding.lean:512 | pairDiagTM_computes and pairDiag_run endpoint | Doubling2n+separator2+rewind(n+2)+copy n+halt1 gives4n+5. Zero-work-space fact is separately merged and cited by Catalog. |
| ClassP/TimeConstructible.lean:356,505,522 | counter_count, lengthBitsTM_computes, lengthBitsTM_spaceUsed | Strengthened prefix head bound pays carries and all-time emission/frozen tail. Time5(n+1) and space5(size n+1) remain literal. |
| TuringMachine/Build/Wrappers.lean:515,717,785,935,1044 | redirectTM_spaceUsedByTape; timed_start, timedCondTM_computes, timed_ledger, timedCondTM_spaceUsed | Unique redirect theorem home; first decider halt; same-input branch; disjoint source/branch/capture tape accounting. |
| TuringMachine/Build/Primitives.lean:2487,3332,3608,3668 | polyUnaryTM_spaceUsed, fwdMapVirtual_run, pairMapSndTM_computes/spaceUsed | e=0 zero tapes. Forwarding parses/rejects before output, monotone payload bounds, one source trajectory's visited sets and2 bounded administrative tapes; no halting premise for space. |
| TuringMachine/Build/Primitives.lean:7814,7900 | unaryTokenTM_computes, appendBitTM_computes | Exact token partition including initial false/unterminated token and empty input; final blank transition included. |
| TuringMachine/Build/Loop.lean:2361,2536,2560,2732,2792,5022 | loopHostTM_contracts, loop_computes_of_startup, loopHostTM_decides/finds/spaceUsed_le_budget, emitLoopTM_computes | Explicit startup cut, positive bounded rounds and orbit invariant. R+1 candidates, first acceptance payload including[], concatenated all-round emission without verdict,10(T+1)(R+2) time and23k(T+1) space. |
| TuringMachine/Build/Loop.lean:3037 | emCall_eval_first final Core correction | Existing public field rewrites followed by intro/cases avoid explicit Option.map definition unfolding. |
| TuringMachine/Build/Catalog.lean:2241,2342 | pairDiag/incFixed constant-space leaves | Both cite exact merged public zero-space facts. Former HOLDs are history. |
| TuringMachine/Build/VirtualInput.lean:299 | generic virtual tagged driver | Set.MapsTo invariant iteration is used. Together with Simulation1093/Primitives3352, there are3 targeted equal-time drivers. |

The frozen current source freeze/runtime/header tables and all-HEAD screen dispositions were read alongside these routes. Other-file theorem statements may be cited without expanding proof values. Unchanged legacy helpers/callers are not represented as entirely newly sealed by this review.
