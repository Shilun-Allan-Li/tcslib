# Gate 03b (one-wayness and collections): round 2 resolutions

- **Round 2:** findings `findings/gate03b-r2-findings.md`, verbatim, SHA-256
  `924a93b01d6ee976c86f602701dbd67f2e77d908b6a1eed264cd46b3a77fbf2a`; pin
  `e79397eaf68b156b9db091f464741f6eb75b9c28`; bundle SHA-256 `1db137f9…` (19 sections). Verdict
  **DO NOT CLOSE: 0 blockers, 1 major, 2 minors.** Round 1's major (#1, canonical decoding) is
  **fixed**. Round 1's rows are fixed, recorded or scheduled, apart from #9 and M6, which
  R2-2 and R2-3 resolve.
- **Repair:** a docstring-only change to `TCSlib/Cryptography/Asymptotic/OneWay.lean` (PR below),
  checked by the maintainer (the 43 modules downstream of `OneWay.lean` plus `Checks`), and one
  record correction.

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | major | **Fixed** (maintainer, true: with `p = var` the zero-padded special outputs `w ‖ 0^k` collide with outputs of `g` ending in `0^k`, so the auditor's inverter succeeds with probability one). `FunFamily.ofString`'s docstring example now follows the auditor's repair. It fixes `p = var` and takes `g(x ‖ b) := h(x) ‖ 1`, so every ordinary output ends in `1` and no zero-padded special output can collide with one. The bound is stated as "at most its success against `g` plus `O(2^{-n/2})`", and the example is marked informal and not formalized. The docstring also says why the final `1` matters. No statement changes; `ofString` itself is unchanged. |
| R2-2 | minor | **Fixed.** `WorstCaseOneWayLit`'s docstring now says the two forms coincide "for families with non-constant `outLen`" and that with constant `outLen` they can differ, as its own examples show. This resolves round 1's #9 in full. |
| R2-3 | minor | **Fixed** (records). `resolutions-03b-r1.md` M6 no longer says the ledger calls the `GGMRed` copy private; DL-15 was corrected on 2026-11-05. |

**Round 3** is a delta audit of the two rewritten docstrings (and the record line).
