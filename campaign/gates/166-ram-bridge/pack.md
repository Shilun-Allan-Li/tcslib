# Gate 166 · Crypto bridge, wave 1: polynomial-time functions from word-RAM programs (PR #379)

**Not yet clear to merge.** PR #379 is a draft into `complexity/ram-simulation`. It carries both
its statements, written by the maintainer, and their proofs (Codex fill `fill-ram-bridge`). This
gate audits both: the statements had no separate statement gate. Seyoon dispatches and merges.

- **Lean head:** `36fd655a964f319877856bbc0fb787ffc217d4ef` (branch `ram/bridge-statements`), on
  the RAM branch's Lean `8d4c1c7e` (#381), which is merged in. The commits:
  1. the statements, `progOut` (proved), and the move of `timeConstructible_poly`;
  2. the fill's proofs, landed unchanged (`fill-ram-bridge.zip` SHA-256 `200cc0e5…`; the patch
     applies and reproduces the delivered files byte for byte);
  3. a merge of the RAM branch;
  4. two maintainer repairs from this gate's runs 1 and 2 (seals, below).
- **Approvals** (Seyoon, 2026-11-18): the bridge items (a1) and (a2), from the RAM bridge
  assessment for the cryptography campaign, and the move of `timeConstructible_poly` out of
  `ClassNP/TMSAT`.

## What it adds

| Module | Declarations | Status |
|---|---|---|
| `Programs/WordRAM/Output` (new) | `progOut P W x`: what `P` emits on `x` at word size `W |x|` with coins `0`, or `[]` if it does not halt. Also `progOut_eq` (via `HaltsWithin.unique`) and `progOut_of_not_halts` | proved |
| `RAMSimulation/Classes` | `polyTimeComputable_of_computes`: a program emitting `g x` within `C·(|x|+1)^d` steps at a word size with `TW n + W n ≤ C·(n+1)^d` makes `g` `PolyTimeComputable`. `polyTimeComputable_progOut`: the same for `progOut P W`, from halting alone | proved modulo `WordRAM.exists_simulation` |
| `RAMSimulation/WordSize` | `wordSizeComputable_of_timeConstructible`, `wordSizeComputable_poly`: polynomial word sizes, in time and space linear in their value | proved, no admission |
| `ClassP/TimeConstructiblePoly` (new) | `Complexity.timeConstructible_poly`, moved from `ClassNP/TMSAT` with its statement unchanged. Its proof now cites the catalog's public `Turing.FinTM.polyUnaryTM` | proved |
| `ClassNP/TMSAT` | the private duplicate of that generator is deleted (about 480 lines). Two private adapters keep `TMSAT_NPHard`'s text byte-identical. The private unary-tape helpers stay | proved |

**Why the generator changed.** TMSAT's private machine was the same machine, with the same
bound, as the catalog's public `Turing.FinTM.polyUnaryTM C e` (`Build/Primitives`):
`C·(|x|+1)^e` ones within `(C + 5e + 4)·(n+1)^e` steps. Moving the theorem with its private
machine would have meant publishing the duplicate, so the theorem cites the public one instead.

## Brief for the auditor

1. **The statements:** that they are true and are the right ones for their purpose. Programs
   written for the word RAM become `PolyTimeComputable` functions; a consumer proves halting on
   every input and correctness where needed (`progOut`).
   - Check uniformity: one program, and a word size that depends only on `|x|`.
   - Check the boundaries: `n = 0`, `d = 0`, `C = 0` where allowed.
2. **The proofs:** the four fill proofs and their sketches, the two repairs, and `progOut_eq`.
3. **The move:** `timeConstructible_poly`'s statement is unchanged (`SOURCE.json`), its new proof
   is sound, and the three existing users still elaborate (the replay). Check that the public
   generator's bound is exactly the deleted machine's.
4. **Admissions:** the two `polyTimeComputable_*` reach only `WordRAM.exists_simulation` (the
   fill's dependency walk, `REPORT-bridge.md`). Nothing else changed reaches an admission.
5. **Rule 10 and duplication:** the seals and the copy screen, below.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl165-cl164`, the branch's build after
  #381. 43 modules: 43 passed, 0 failed. It includes TMSAT's downstream (Cook–Levin, the NTIME
  hierarchy, P ⊆ P/poly). There are 2 admissions in the replayed sources, the stage-2 targets.
- **Seals:** run 3 passes, 8 proofs and 13 heads. Runs 1 and 2 (carried in the data carrier)
  found the moved `timeConstructible_poly` reading `TimeConstructible` and `ComputesFunInTime`
  directly, and the edited `TMSAT_NPHard` reading `NPHard`. Repairs: `timeConstructible_poly`
  goes through `timeConstructible_iff` and `computesFunInTime_iff`, and `TMSAT_NPHard` is restored
  byte for byte behind private adapters, so it is no longer a changed proof.
- **Controls:** 24 definitions and 48 identities, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 0 read candidates. Citation homes are in
  `CITATION-HOMES.json`; all are in the bundle.
- **Copy screen:** 10 → 8 pairs, 0 new. The two gone pairs were phases of the deleted duplicate
  machine (`pair-notes.json`).
- **The fill's report** (`REPORT-bridge.md`): axiom prints and its dependency walk.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate166-ram-bridge-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
