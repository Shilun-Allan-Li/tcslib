"""The review's proposed edits to the NF cont1 draft, each asserted to apply exactly once.
usage: python3 -I edits.py <orig.md> <edited.md>"""
import sys

src, dst = sys.argv[1:3]
t = open(src, encoding='utf-8').read()

E = []

# F10: the base's Lean, not only the owned blob
E.append(('F10', '''  git rev-parse HEAD:TCSlib/Complexity/ClassNP/NDNormalForm.lean
  # must print e6432b1e6cf6eb33f81bff05eb389b09dd7cb9f0
  ```''', '''  git rev-parse HEAD:TCSlib/Complexity/ClassNP/NDNormalForm.lean
  # must print e6432b1e6cf6eb33f81bff05eb389b09dd7cb9f0
  git diff --quiet 5241eb8257bdeb5b5c274145575749dd186ec65f HEAD -- '*.lean' && echo same-Lean
  # must print same-Lean: your base's Lean is that of the first round's branch tip
  ```'''))

# F9 (and F13): rv_tag's file; rv_skeleton
E.append(('F9a', '''    The first round's inputs (`campaign/fills/c1/inputs/c1-fill-nf/`) still apply, in particular
    `NFReviewProbe.lean.txt` (`rv_entry`, `rv_tag`, `rv_inputSymbol_congr`,
    `rv_moveInputPos_le`) and `NFReviewVProbe.lean.txt` (`rvPark`).''',
'''    The first round's inputs (`campaign/fills/c1/inputs/c1-fill-nf/`) still apply, in particular
    `NFReviewProbe.lean.txt` (`rv_entry`, `rv_inputSymbol_congr`, `rv_moveInputPos_le`, and
    `rv_skeleton`: the target assembled from the obligations on `V`, sealed, the model for
    checkpoint 8) and `NFReviewVProbe.lean.txt` (`rv_tag`, `rvPark`).'''))

# F8: the brief's tape names are not library vocabulary
E.append(('F8', '''  campaign labels ("NF", "checkpoint", "cont1", "sweep 0"), dates or session narrative; provenance
  goes in `REPORT.md`. The replay leaf's docstring says which public rows it is not and what was
  missing (`policy.md` §1): `scanTM` reads one tape, and `StepBlock`'s `recordTM` reads records on
  `k + 2` tapes;''', '''  campaign labels ("NF", "checkpoint", "cont1", "sweep 0"), dates or session narrative; provenance
  goes in `REPORT.md`. "A" and "B" are this brief's names, not the library's: in docstrings write
  tape `0` (the stream) and tape `1` (the replay tape). The route probe's docstrings use "A" and
  "B"; rewrite them when you copy its layout. The replay leaf's docstring says which public rows
  it is not and what was missing (`policy.md` §1): `scanTM` reads one tape, and `StepBlock`'s
  `recordTM` reads records on `k + 2` tapes;'''))

# F15: region (d)'s lines
E.append(('F15', '''- **(d)** at completion only: the module docstring's and the target docstring's status phrases
  (public-facing; no campaign labels).''', '''- **(d)** at completion only: the module docstring's and the target docstring's status phrases
  ("(statement; proof incomplete)", lines 30–31, and "statement; proof incomplete", line 707;
  public-facing; no campaign labels).'''))

# F3: nfc_aReturn's generalization
E.append(('F3a', '''`nfc_aReturn` is A's return chained through `phaseHostTM_run`, `nfc_retag` the step from a
redirected configuration to the next phase's start. Keep both, renamed.''',
'''`nfc_aReturn` is A's return chained through `phaseHostTM_run`, `nfc_retag` the step from a
redirected configuration to the next phase's start. Keep both, renamed. `nfc_aReturn` is stated
for the input's return: state it once for every replayed tape, whose last redirect is
`nfcAfter N L none` for the input and `⟨.bFwd j, .run⟩` for work tape `j`.'''))

# F6: the named instances, as the probe has them
E.append(('F6', '''**Named instances (pinned).** `DecidableEq` and `Fintype` for the control sweep's `ScanPhase
(nf_SweepState N)` (as `@instDecidableEqScanPhase _ inferInstance`), the leaf's state, the phase
family and `V`'s state, each as a `private instance` (or `local instance`). Default synthesis does
not reach `DecidableEq (ScanPhase (nf_SweepState N))` at the default instance size (the review's
F3). Never raise `synthInstance.maxSize` instead.''',
'''**Named instances (pinned).** As in the probe: `DecidableEq` and `Fintype` for the phase family's
fibers (`nfcStDecEq`, `nfcStFintype`), with the control sweep's `ScanPhase (nf_SweepState N)`
inside them (`@instDecidableEqScanPhase _ inferInstance`, `@instFintypeScanPhase _ inferInstance`),
and for the leaf's state, each as a `private instance` (or `local instance`). `V`'s state then has
both by inference (the probe's two `example`s). Default synthesis does not reach
`DecidableEq (ScanPhase (nf_SweepState N))` at the default instance size (the review's F3). Never
raise `synthInstance.maxSize` instead.'''))

# F1 (major): every record writes its block
E.append(('F1a', '''- **A work-tape instance** keeps tape `j` on B as two-bit blocks: a visited cell is two nonblank
  bits encoding its `Option Bool` content, an unvisited cell two blanks. B's head sits at twice
  the simulated head, so a simulated move is two cells on B. It checks each decoded claim against
  B's block, then writes the recomputed write.''',
'''- **A work-tape instance** keeps tape `j` on B as two-bit blocks: a visited cell is two nonblank
  bits encoding its `Option Bool` content, an unvisited cell two blanks. B's head sits at its
  start position plus twice the simulated head, so a simulated move is two cells on B. It checks
  each decoded claim against B's block, then **writes the block at every record**: two nonblank
  bits encoding the cell's content after the step, `(a.workTapes j).1.getD old` (the shape of
  `Action.apply_workTapes`). An action that writes nothing (`(a.workTapes j).1 = none`) still
  writes its block, so an unvisited cell under the head becomes the nonblank code of blank.
  Otherwise the visited region can have blank holes, and B's clear either does not apply or leaves
  cells that a later work tape's replay reads, rejecting a genuine display.'''))

# F3: where the pass exit leaves A's head
E.append(('F3b', '''- **Its exits** are A's blank after `s` (pass) or a reject state.''',
'''- **Its exits** are a pass state, entered after the end-flagged record with A's head on the blank
  after `s` (cell `|s|`, not past it: `nfc_aReturn`'s `hpos`), or a reject state.'''))

# F2: the exit invariant, precisely
E.append(('F2', '''- **The exit invariant on B (pinned).** At a work-tape instance's exit, B's head is on a cell of
  the nonempty, contiguous, nonblank visited region. `skipTM_run_ofCfg` started left of the region
  ends on its first cell, so B's clear would not apply otherwise. The head can leave the region
  only by the last record's move to the left. **Keep the invariant by not performing the
  end-flagged record's head move** (the leaf knows the record is the last when it completes it,
  and that move affects no later check), or else by the first round's proposal: initialize a
  previously blank destination block as two nonblank bits encoding blank. Say which in
  `REPORT.md`.''',
'''- **The exit invariant on B (pinned).** At a work-tape instance's exit, B is blank outside the
  visited region, which is nonempty, contiguous and nonblank (every record writes its block), and
  B's head is on a cell of it. B's clear also applies from the region's right delimiter, but not
  from the block left of the region: there `skipTM_run_ofCfg` at `w := []` ends on the left
  delimiter, and `skipBackTM_run_ofCfg` at `u :=` the region does not apply. Since every record
  writes its block, the head can leave the region only by the last record's move, and only a
  move to the left is harmful. **Keep the invariant by not performing the end-flagged record's
  head move** (the leaf knows the record is the last when it completes it, and that move affects
  no later check), or else by the first round's proposal: initialize a previously blank
  destination block as two nonblank bits encoding blank. Say which in `REPORT.md`. If the work
  tape's head never moves, the region is the one block at B's start.'''))

# F9: the authorized transcriptions' files
E.append(('F9b', '''**Authorized transcriptions** (from `NFReviewProbe.lean.txt` and `NFReviewVProbe.lean.txt`, as
`nf_pack` and `nf_setup` were; renamed `nf_`):''',
'''**Authorized transcriptions** (`rv_entry`, `rv_inputSymbol_congr` and `rv_moveInputPos_le` from
`NFReviewProbe.lean.txt`, `rv_tag` and `rvPark` from `NFReviewVProbe.lean.txt`, as `nf_pack` and
`nf_setup` were; renamed `nf_`):'''))

# F5: the ledger, without double counting
E.append(('F5', '''- each return of A, `|s| + 6`;
- each clear of B, `O(t₀)`;
- one step per redirect.''',
'''- each return of A, `|s| + 6`, its two redirects included (`nfc_aReturn`);
- each clear of B, `(|R| − i + 1) + (|R| + 3) + (2|R| + 2)` with `R` the region and `i` B's
  head's offset in it, plus its three redirects: `4|R| − i + 9 = O(t₀)`;
- one step for each other redirect (after the control sweep and after each replay).'''))

# F1: the edge cases
E.append(('F1b', '''- a work-tape write of a blank: the block encodes `none` and stays nonblank;''',
'''- a work-tape write of a blank: the block encodes `none` and stays nonblank;
- a work-tape action that writes nothing: its block is still written, so the region has no hole;
  a work tape whose head never moves: the region is one block;'''))

# F7: derived instances of a private type
E.append(('F7', '''    file. Keep your new privates under the `nf_` prefix, clear of the 39 existing names. A
    `private inductive` with `deriving DecidableEq` gets a public instance name: write the
    instance as a `private instance` instead, or check that no file or open PR has the name, and
    report it.''',
'''    file. Keep your new privates under the `nf_` prefix, clear of the 39 existing names. A
    `private inductive` with `deriving` gets public instance names: the probe's phase index gets
    `Turing.FinNDTM.instDecidableEqNfcPh` and `Turing.FinNDTM.instFintypeNfcPh`, with their
    auxiliaries. These are public constants, not public declarations (`workflow.md` §4, counting
    public names): check that no file or open PR has your renamed ones and report them, or write
    the instances as `private instance`s.'''))

# F4: the layout lands with checkpoint 3
E.append(('F4', '''3. **The input's replay:** the leaf, its run lemma at the input instance, A's return after it.''',
'''3. **The input's replay:** the leaf, its run lemma at the input instance, `V`'s layout (generic
   over the leaf, as in the probe), A's return after it.'''))
E.append(('F4b', '''5. **`V`:** the layout, its characterization, `hV`, and its verdict on a display.''',
'''5. **`V`:** its characterization, `hV`, and its verdict on a display.'''))

# F14: the one-step identity needs no new lemma
E.append(('F14', '''    `recordStep_runFrom_one`): if you need it, state it once and list it as a promotion request;''',
'''    `recordStep_runFrom_one`): `MultiTapeTM.runFrom_succ_eq_step'` at `t := 0` and `runFrom_zero`
    give it in one `rw`, so no lemma is needed;'''))

# F11: the checklist
E.append(('F11', '''- [ ] The checkpoints reached (3–8), **one zip each**, and the base hash.''',
'''- [ ] The checkpoints reached (3–8), **one zip each**, the base hash and the ancestor check; if
      the session stopped before checkpoint 8, what ended it.'''))

for tag, old, new in E:
    n = t.count(old)
    assert n == 1, (tag, n)
    t = t.replace(old, new)
open(dst, 'w', encoding='utf-8').write(t)
print('applied', len(E), 'edits:', ' '.join(tag for tag, _, _ in E))
