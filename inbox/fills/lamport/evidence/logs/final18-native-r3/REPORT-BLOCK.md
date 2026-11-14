Final18 native verification at47ced271090f45918645c842cd358c5079092754 is complete. All18 standard A source seals passed with zero errors. Strict B passed16 phases and failed2 phases with32 mapped diagnostics; these failures are reported explicitly below. All102 sensitivity controls passed:34 negative controls produced exactly one error at the expected line, and68 positive controls produced zero errors. Blocks has no TCSlib closure and therefore has no controls; Averaging and AveragingExtra use the qualified ProbComp.expect fallback controls.

All18 snapshots and18 exact-closure native collectors exited0. All321 stored own constants, including generated/private constants, have axiom sets contained in {propext, Classical.choice, Quot.sound}. Every requested name/home/reducibility check completed at INSTALL and EOF. All177 frozen TCSlib source hashes remain byte-identical to the successful final-r2 sweep at47ced; no TCSlib source was edited. No native resource retries occurred in this final queue.

Strict B adds PolyExpr.eval to the same sealed request sets. In Realization, the first type conversion failures occur at source146 in the new exists_realization_machine proof: Fin n / Fin(n*n) arguments do not convert to bitSpecAt(var,var.mul var)n domain/range when eval is opaque. The other failures concern the same oracle specification or output-vector widths. These new helper diagnostics are not classified as inherited baseline failures.

In the main file, the first failure is at source499 in lamportOWF: its f accepts Fin n, while the declared FunFamily input expects Fin(PolyExpr.var.eval n). A second width conversion appears at598 in lamport correctness. Later declarations report type/notation/context cascades from the failed declarations, including the target theorem. This strict-B result is not a passing proof of those declarations under opaque eval. The standard A source seal and ordinary native proof remain passing.

Every strict-B failing declaration and all its mapped source error lines:

| File | Declaration | Original source lines |
| --- | --- | --- |
| TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean | TCSlib.Cryptography.Authentication.LamportFill.exists_realization_machine | 146, 153, 174, 177, 179 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport | 598 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF | 499 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_f | 508 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_inLen | 502 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_outLen | 505 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_exists_best_position | 876, 881 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability | 826 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_forgerCodec | 766 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_gen | 607 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect | 807, 810 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_msgLen | 601 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_oneTimeSecure | 917, 918, 921 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_sigLen | 604 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_sign | 610 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_signImpl_expect | 791 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_ver | 613 |

Complete raw source/collector/seal/control logs, immutable probe sources and line maps, actual-generator provenance, tool snapshots, request inventories, scans, and per-phase summaries are retained in evidence. Canonical aggregate: logs/final18-native-r3/native-totals.json. Full32 mapped diagnostics with raw-log/result links: logs/final18-native-r3/strict-b-failures.json. Native queue: preparation/final18-r2/cached-collectors-r3/queue.json. Historical uncached attempts, cache qualification attempts, the retired coordinator record, and previous tool/collector versions remain preserved.
