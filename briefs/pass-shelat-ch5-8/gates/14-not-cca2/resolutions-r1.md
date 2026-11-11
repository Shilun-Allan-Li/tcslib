# Gate 14 · resolutions, round 1

**Status: CLOSED** (0 blockers, 0 majors, 1 minor, fixed). Auditor Codex, 2026-11-11; findings
uploaded by Seyoon and filed verbatim in [findings/](findings/gate14-not-cca2-findings.md)
(SHA-256 `71f59c6f3486bc44c21de21fc07700db049a588f79c81af62ae475fa2fafa42f`).

| Input | Pin |
|---|---|
| Exchange pack | `35c6ffb76b0b6a679680396a7f7b86843a5eafda` |
| PR #289 Lean head | `7960d6d4c3254797fdec191fff72c8d4c0147e1a` |
| Records | `de2f7f0e890f0cdb972b4d5258c4e8f569cdcb1a` |
| Landing base | `fe757f17aa6bda2f711e69abe7e2470ce5872e04` |

The auditor verified all pack, bundle, source and archive hashes and the statement freeze, and
reviewed the proof (adversary, budget and CCA2 legality, ciphertext and decryption frontier, the
advantage). It also **independently rebuilt** the 129-module target closure at the final source
(Lean 4.25.0, Mathlib `029db123`), printed the axioms of both theorems and all seven readers
(standard), re-ran the three whole-file seals (1,754 / 678 / 1,842 requests) and the 6 control
probes at the final source, and ran the style lint (0 FAIL).

| # | Severity | Resolution |
|---|---|---|
| G14-01 | minor | **Fixed.** The landing axiom log is regenerated with the correct names at head `7960d6d4` (`landing/axioms-r2.log`): rc 0, no errors; `prfFixedScheme_not_cca2`, `not_prfFixedScheme_cca2`, `TCSlib.Cryptography.prfScheme_dec` and the six readers each depend on exactly `[propext, Classical.choice, Quot.sound]`. The earlier `landing/axioms.log` is kept as superseded. |

**Clear to merge** — #289 at `7960d6d4c3254797fdec191fff72c8d4c0147e1a`.
