**U2: the `k`-tape universal machines, proved** (the landing of `fill-u2s-universal.zip`;
[AB09, §1.4.1, Theorem 1.9; Exercise 4.1]).

`TuringMachine/UniversalK`'s two sorried contracts are proved, both on `[propext,
Classical.choice, Quot.sound]`:
- `Turing.exists_selfUniversalK`, the self-application universal machine: time `C · (t + 1)`,
  space `C · (s + 1)` and the converse. `C` is per code.
- `Turing.universalK`, the code-first evaluator: time `C · (t + 1)` with no `|x|` term, and the
  converse. It runs the startup first, then a finite-state header scan writes a ruler, and the
  ruler host `Turing.exists_rulerHostTM` runs the forwarding loop.

With them, `Turing.exists_selfUniversal` (`SelfUniversal`, the `k = 1` case) is admission-free.

**The commits:**
- 5 commits, the delivery's series, cherry-picked unchanged (the worker's authorship and subjects
  kept). They reproduce the delivered file byte for byte.
- `fd995ec1`, the review's landing edits:
  - three inline arguments that re-proved published lemmas now cite them:
    `MultiTapeTM.exists_first_halt`, `MultiTapeTM.visitedByTapeHead_mono` and
    `FinTM.ComputesInTime.spaceUsed_le_of_halt` (the review's F1, −28 lines);
  - `UniversalK`'s header and main results, `SelfUniversal`'s status and the facade's entries say
    the contracts are proved;
  - `universalK`'s docstring gains an `**Implementation.**` paragraph naming the rows and the
    constant.

| Check | Result |
|---|---|
| Elaboration | the review: the delivered file with no diagnostic at the base (`oleans-lkit2`), and this head's three files with no diagnostic at the tip after #165 (`oleans-lg4c4m`; byte-identical to this branch) |
| Axioms | both targets, all 28 new privates and `exists_selfUniversal`: the standard three |
| Freeze | 12 → 12 public, no statement changed; 39 → 67 private (28 new `uk_`, none removed or changed); `SelfUniversal` and the facade: header text only |
| Rule 10 | the review's seal (27 other-file definitions, two `simp` erasures, two instances): the body has 0 errors, all 31 controls bite; no other-file definition passed to `rw`/`simp`/`unfold` |
| Rule 11 | clean |
| Duplication | text screen (the brief's 20-file population): 788 → 793 pairs, 5 new, all inside `UniversalK`, none at 90% or more, no cross-file pair. Semantic: F1 fixed here |
| Lint | `TuringMachine` 0 FAIL, 67 WARN over 84 files, as at the base; widths ≤ 99 |
| Sweep | the worker's 97-module sweep: 26 → 24 sorry warnings, exactly the base set less the two targets |

**The user's rulings (2026-10-26):**
- D1–D3 (F1) and every wording edit (S1–S6) land here;
- the ruler on tape `k + 2` (F2) and the grouped checkpoint zips (F5) are accepted;
- this PR merges after #164 and #167.

**Replay:** `UniversalK`, `SelfUniversal` and the `TuringMachine` facade (3 modules). It is chained
from the snapshot #164's and #167's replays leave, after the campaign is merged in. **Pending.**

**Gate:** a fill gate (gate 80, `campaign/gates/80-u2-universal-fill/`). **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
