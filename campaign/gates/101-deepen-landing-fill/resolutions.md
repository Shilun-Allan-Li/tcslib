# Gate 101 (#208, the deepening fill's landing): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (attached in chat by the user), SHA-256 `9cac0aa6e87b7e024009c0b870dbabf1c499a3853ce8492f314e47774cdf68bf`.

**Verdict: HOLD — 0 blockers, 1 major, 3 minors, 3 notes.** No soundness defect.

**F1 ruled (the user, 2026-11-06): harvest in #208, all three.** The bound
`m ≤ 2^e + 1 → (Nat.bits (m + 1)).length ≤ e + 2` is published in `Machines/Bin` beside
`length_bits_le`, and `Deepen`'s `deepen_contract`, `ARMWidth`'s inline block and
`ISCountGenCorrect`'s private `bits_succ_le` are re-pointed to it inside #208.
