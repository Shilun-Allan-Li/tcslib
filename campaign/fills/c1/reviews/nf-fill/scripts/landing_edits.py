"""Apply the review's landing edits E1-E3 to the head's owned file, asserting each (python3 -I).
E1 removes one blank line from each double blank line; E2 rewords five docstrings (the control
sweep instead of "sweep 0/zero", tape `0` instead of "A", the width named, the final flag stated); E3 adds an
**Implementation.** paragraph to the target's docstring.
usage: python3 -I landing_edits.py <head.lean> <out.lean>"""
import sys
src, out = sys.argv[1:3]
t = open(src, encoding='utf-8').read()
def rep(old, new, count=1):
    global t
    assert t.count(old) == count, (t.count(old), old[:80])
    t = t.replace(old, new)
# E1: the four double blank lines (head 91-92, 540-541, 584-585, 626-627)
rep('\n\n\n', '\n\n', 4)
assert '\n\n\n' not in t
# E2: docstring wording
rep('/-- Sweep zero begins at the start state with an empty record and output summary. -/',
    '/-- The control sweep begins at the start state with an empty record and output summary. -/')
rep('''/-- **Sweep 0 is the published scan fold.** From the entry configuration with the scan's
forward state, the scan on tape `0` reaches the completed bit fold at
exactly `2|s| + 2`, not at any `done` before, with every tape, head, the input head and the
output as at the entry: A's head is back at `0` with no separate rewind.''',
    '''/-- **The control sweep is the fold instance of `Turing.scanTM`.** From the stream start with
the scan's forward state, the scan on tape `0` reaches the completed bit fold at exactly
`2|s| + 2`, not at any `done` before, with every tape, head, the input head and the output as at
the start: the head of tape `0` is back at cell `0` with no separate rewind.''')
rep('/-- Sweep zero passes the display of a branch that first halts at its end with output',
    '/-- The control sweep passes the display of a branch that first halts at its end with output')
rep('''**Proof sketch.** The final cell of record `r` has index `W(r+1)-1`. Its quotient by `W`
is `r` and its remainder is `W-1`, so the record encoder returns the prescribed end flag. -/''',
    '''**Proof sketch.** With the width `W = 2k + 4`, the final cell of record `r` has index
`W(r+1)-1`. Its quotient by `W` is `r` and its remainder is `W-1`, so the record encoder returns
the prescribed end flag. -/''')
rep('''/-- A stream that first stops the controller consists of a positive number of complete
records, with false end flags on all but the final record.''',
    '''/-- A stream that first stops the controller consists of a positive number of complete
records, with false end flags on all but the final record, whose end flag is true.''')
# E3: the target's Implementation paragraph
rep('''`exists_codeTM` precedent). Fill obligations, named: the display format and
its on-the-fly control check; the `k + 1` verification sweeps; the two
transfer directions; the relabeling packaging. -/''',
    '''`exists_codeTM` precedent). Fill obligations, named: the display format and
its on-the-fly control check; the `k + 1` verification sweeps; the two
transfer directions; the relabeling packaging.

**Implementation.** The display refines the sketch: one record of `2k + 4`
bits per step of `N`, holding the step's choice bit, the claimed input and
work-tape reads (two bits each: `00` blank, `10` false, `11` true) and an end
flag, set on the last record only. States and actions are not guessed: the
verifier recomputes them from `N`'s table in its finite control. The guess
runs under the controller-stopped host `Turing.guessCtlRunTM` with a trivial
setup; its controller stops at the first record boundary after a set end
flag. The verifier is deterministic and silent: a control sweep (a fold by
`Turing.scanTM`) checks the recomputed states, the end flags and the output,
and replay sweeps check the claimed reads against the input and, on the
second work tape, against each replayed work tape, which `Turing.skipTM`,
`Turing.skipBackTM` and `Turing.clearTM` then erase. -/''')
for w in ('Sweep 0', 'Sweep zero', "A's head", 'published'):
    assert w not in t, w
assert max(len(l) for l in t.split('\n')) <= 100
import re
assert not [l for l in t.split('\n') if re.match(r'(instance|theorem|lemma|def|abbrev|end|namespace|section|open|structure|inductive|class)\s+(of|the|a|an|by|at|is|on|in)\b', l)], 'a docstring line starts with a keyword'
open(out, 'w', encoding='utf-8').write(t)
print('wrote', out, len(t.split('\n')) - 1, 'lines')
