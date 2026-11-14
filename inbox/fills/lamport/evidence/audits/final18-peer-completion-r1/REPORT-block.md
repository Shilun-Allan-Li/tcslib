All eighteen final whole-file Rule 10 reviews are complete for `47ced271090f45918645c842cd358c5079092754`.

| File | Own constants | Closure | A/B definitions | A/B errors | Controls | Scan readings/candidates |
|---|---:|---:|---:|---:|---:|---:|
| Planted | 67 | 100 | 1438/1439 | 0/0 | 6 | 150/3 |
| Encoding | 3 | 53 | 813/814 | 0/0 | 6 | 6/0 |
| TableCoins | 6 | 101 | 1455/1456 | 0/0 | 6 | 8/0 |
| Averaging | 7 | 3 | 38/38 | 0/0 | 6 | 30/0 |
| AveragingExtra | 3 | 9 | 50/50 | 0/0 | 6 | 7/0 |
| Statistics | 2 | 102 | 1455/1456 | 0/0 | 6 | 18/0 |
| Experiment | 23 | 107 | 1462/1463 | 0/0 | 6 | 38/2 |
| Advice | 12 | 67 | 911/912 | 0/0 | 6 | 34/0 |
| Blocks | 2 | 0 | 0/0 | 0/0 | 0 | 31/0 |
| Closing | 4 | 78 | 1057/1058 | 0/0 | 6 | 12/0 |
| InversionProbability | 2 | 108 | 1468/1469 | 0/0 | 6 | 17/0 |
| Machine | 73 | 138 | 1930/1931 | 0/0 | 6 | 46/0 |
| Seed | 6 | 102 | 1456/1457 | 0/0 | 6 | 6/0 |
| MachineSpec | 13 | 148 | 2003/2004 | 0/0 | 6 | 175/5 |
| Nonabort | 1 | 101 | 1455/1456 | 0/0 | 6 | 11/0 |
| Realization | 6 | 156 | 2014/2015 | 0/6 | 6 | 77/8 |
| Lamport | 91 | 163 | 2025/2026 | 0/26 | 6 | 386/32 |
| Auth | 0 | 176 | 2149/2150 | 0/0 | 6 | 0/0 |

All eighteen A seals pass. All 102 controls pass, including 34 sealed negatives with exactly one error each. The 321 stored constants have only subsets of `{propext, Classical.choice, Quot.sound}` as axioms. All 50 scanner candidates were reviewed in their source contexts; none is a forbidden explicit foreign unfold. Blocks has no TCSlib import closure and therefore zero requested definitions and no closure-local control; the other seventeen phases supply the paired controls.

B failures (with `PolyExpr.eval` sealed):

- `TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization`: 6 errors in 1 declarations: `TCSlib.Cryptography.Authentication.LamportFill.exists_realization_machine`.
- `TCSlib.Cryptography.Authentication.Signatures.Lamport`: 26 errors in 16 declarations: `TCSlib.Cryptography.Authentication.lamport`, `TCSlib.Cryptography.Authentication.lamportOWF`, `TCSlib.Cryptography.Authentication.lamportOWF_f`, `TCSlib.Cryptography.Authentication.lamportOWF_inLen`, `TCSlib.Cryptography.Authentication.lamportOWF_outLen`, `TCSlib.Cryptography.Authentication.lamport_exists_best_position`, `TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability`, `TCSlib.Cryptography.Authentication.lamport_forgerCodec`, `TCSlib.Cryptography.Authentication.lamport_gen`, `TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect`, `TCSlib.Cryptography.Authentication.lamport_msgLen`, `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`, `TCSlib.Cryptography.Authentication.lamport_sigLen`, `TCSlib.Cryptography.Authentication.lamport_sign`, `TCSlib.Cryptography.Authentication.lamport_signImpl_expect`, `TCSlib.Cryptography.Authentication.lamport_ver`.

Per-name INSTALL and EOF multisets, actual Name/home identity, original-source maps and hashes, full eligible-set selection (including private definitions and generated matchers), exact runtime import closure, every own axiom row, and control locations were checked against the retained raw evidence. The versioned module-name cache changes only pure reads of a captured immutable environment. Earlier Core-loop/sparse proposals were not adopted; historical attempts and the actual generator bindings are preserved.
