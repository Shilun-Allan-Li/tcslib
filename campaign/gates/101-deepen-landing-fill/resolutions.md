# Gate 101 (#208, the deepening fill's landing): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (attached in chat by the user), SHA-256 `9cac0aa6e87b7e024009c0b870dbabf1c499a3853ce8492f314e47774cdf68bf`.

**Verdict: HOLD — 0 blockers, 1 major, 3 minors, 3 notes.** No soundness defect.

**F1 ruled (the user, 2026-11-06): harvest in #208, all three.** The bound
`m ≤ 2^e + 1 → (Nat.bits (m + 1)).length ≤ e + 2` is published in `Machines/Bin` beside
`length_bits_le`, and `Deepen`'s `deepen_contract`, `ARMWidth`'s inline block and
`ISCountGenCorrect`'s private `bits_succ_le` are re-pointed to it inside #208.

### Round 1 dispositions (#208's commit `9db4f2ee`, then the campaign merge `dd8a52c5`)

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Fixed (the ruling).** `Complexity.LogProg.length_bits_succ_le` in `Machines/Bin` (statement `m ≤ 2 ^ e + 1 → (Nat.bits (m + 1)).length ≤ e + 2`, with a sketch and the module's results list); `ISCountGenCorrect`'s private `bits_succ_le` deleted and its one use re-pointed; `ARMWidth`'s `arm_decides_pspace_val` and `Deepen`'s `deepen_contract` cite it in place of their `hlt` blocks. The family is recorded as **BL-2** in `campaign/duplication-ledger.md`, retired on #208's merge. |
| 2 | minor | **Fixed in part, the rest recorded.** `savitch` reads `SpaceConstructible` through `spaceConstructible_iff` (`((spaceConstructible_iff S).mp hS).1`). The two remaining reads are exceptions: `rintro L ⟨c, N, hN⟩` destructures `NSPACE`'s set-builder body, which has no published characterization (no `mem_NSPACE_iff`; the library's other `NSPACE` consumers, such as `compl_mem_NSPACE`, read it the same way); `obtain` reads `DeepenContract`, whose `_iff` the brief forbids as a fourth public declaration (the pack's check-8 WARN). Round 2's seal covers `Deepen` only; it does not establish rule 10 for `Savitch.lean`. |
| 3 | minor | **Fixed.** `Savitch.lean`'s Design bullet and `PSPACE_eq_NPSPACE`'s sketch give the register bound as `2 ^ (w · w)`, so `O(w²)` digits; `dp_run`'s sketch bounds the setup values by `max |x| (1 + |bits |x||)`, below `2 ^ dpW`, and the loop's by `2 ^ (dpW · dpW)`. |
| 4 | minor | **Fixed.** `deepen_contract`'s docstring states that the machine never computes `sp` and searches at radius `1, 2, …` until no configuration reaches the window's edge, tagged [Sip13, §8.1, proof of Theorem 8.5] and [AB09, Theorem 4.14]; its sketch cites `length_bits_succ_le`. |
| 5 | note | No change. |
| 6 | note | No change. |
| 7 | note | No change; round 2's pack keeps the distinction between repeated static checks and inspected execution records. |

### Found in round 2's preparation

**IL-1** (`campaign/duplication-ledger.md`): round 2's screen adds the two newly changed files
(`ISCountGenCorrect`, `Machines/Bin`) to round 1's 20, and pairs `ISCountGenCorrect`'s `gen_start`
with `InputAccess`'s `indicator_inputLenLang` and `ExpBFS/Main`'s `orcN_len` (94%, present at the
base). `git grep` for the closing step found four more members. **Ruled (the user, 2026-11-06):
re-point all six in #208**, done at `6a289c50`.

**IL-1 widened** (the same preparation): the first search matched one closing form only. Five
more members re-derive `indicator_inputLenLang` or its sibling `indicator_inputBitLang` through a
simp set (`PathWalkMachine`'s `pathOr_len`/`pathOr_bit`, `PathHardRegs`' `orc_bit`, `Mult`'s
`mult_queries`). **Ruled (the user, 2026-11-06): re-point all five in #208**, done at `0140aee2`;
the ledger's IL-1 is widened by kind to both readings.

## Round 2 findings (received 2026-11-06)

`findings-r2.md`, verbatim (from the exchange inbox), SHA-256
`7685adea2675655e227ccd6ed40213b09a379a3e7af0a53d58f54e0902014d2c`.
**Verdict: PASS — 0 blockers, 0 majors, 1 minor, 4 notes. The gate closes.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed** in the ledger: IL-1's census is 10 declarations across eight files, 11 proof sites. |
| 2–5 | note | No change. |
