# Fill report · `padded-cpa` · checkpoint 1

**Worker** Claude. **Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on
`cryptography/pass-shelat-ch2-4` (local proof branch `fill/padded-cpa`, not pushed).
**Pack** verified at exchange `cc07d65f9` (`sha256sum -c SHA256SUMS`: all 7 OK).

## Status at this checkpoint

**`BitPublicKeyScheme.SingleBitSecure.padded_cpa` is proved** (no `sorry`), at proof-branch
`747b9c2a7`. Steps 1–4 of the brief landed together, so this checkpoint covers all four:

| Step | Where |
|---|---|
| 1 eager challenge coins | `expect_simulate_indImpl_cpa` (private, `OracleSecurity.lean`) |
| 2 first-challenge congruence | `ChallengeSim.chRun_congr` (`OracleSecurity/ChallengeSim.lean`) |
| 3 distinguisher `D` via T1 | `ChallengeSim.recHandler` (`OracleSecurity/RecordHandler.lean`) + `exists_handlerMachine` |
| 4 exact identity | `padded_cpa_advantage_eq` (private, `OracleSecurity.lean`) |

Checked so far (one module per `scripts/lean_check_tree.sh` call): `ChallengeSim`,
`RecordHandler`, `PublicKey/OracleSecurity`: exit 0, no warnings (`evidence/logs/dev-checks.log`).
Axioms of `padded_cpa`: `[propext, Classical.choice, Quot.sound]` (`evidence/logs/axioms.log`).
Style lint on `Encryption/PublicKey --check8b`: 0 FAIL; no WARN on the touched files.

**Order change (to be detailed in the final report).** `OracleSecurity` now imports
`Games.Efficiency` (T1) and `Games.Bridges.Experiments`; their closure adds 10 modules that were not
in the issued `order.txt`, plus the two new helpers, all inserted before
`PublicKey/OracleSecurity` (`evidence/logs/order-new.txt`, 233 modules, topologically checked). No
new Mathlib root.

**Pending for the final payload:** `TrapdoorCPA` recheck and the full sweep, sorry census against
`base-sorries.txt`, `tdpBitScheme_padded_cpa` axioms, the foreign-reference scan, seal and
controls, the explicit-unfold scan.
