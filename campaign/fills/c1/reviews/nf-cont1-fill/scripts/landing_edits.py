# landing_edits.py <head module> <out>: the review's landing edits E1-E6, each asserted.
import re, sys
src, out = sys.argv[1:3]
t = open(src, encoding='utf-8').read()
def rep(tag, old, new, count=1):
    global t
    n = t.count(old)
    assert n == count, (tag, n)
    t = t.replace(old, new)
    print(f'{tag}: replaced {n}')
# E1: nf_all_cons is Mathlib's Nat.forall_lt_succ_left' (cite it instead of re-deriving it)
rep('E1', '''      P c rec ∧ ∀ r (h : r < rs.length),
        P ((rs.take r).foldl (nf_vstep N) (nf_vstep N c rec)) rs[r] := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun r hr => h (r + 1) (by simp; omega)⟩
  · rintro ⟨h0, h⟩ r hr
    cases r with
    | zero => exact h0
    | succ r => exact h r (by simp at hr; omega)
''', '''      P c rec ∧ ∀ r (h : r < rs.length),
        P ((rs.take r).foldl (nf_vstep N) (nf_vstep N c rec)) rs[r] :=
  Nat.forall_lt_succ_left'
''')
# E2: the dangling reference
rep('E2', "configuration's read, it is `N`'s step under the record's choice bit (`nf_vstep_genuine`). -/",
    "configuration's read, it is `N`'s step under the record's choice bit (`nf_vrun_of_ok`). -/")
# E3: nf_vrun_ctl states the output summary too
rep('E3', "/-- The control fold's state follows the decoded virtual run, over a list of records. -/",
    "/-- The control fold's state and output summary follow the decoded virtual run, over a list of\nrecords. -/")
# E4: no campaign word in the section name
rep('E4a', '\nsection Continuation\n', '\nsection\n')
rep('E4b', '\nend Continuation\n', '\nend\n')
# E6: the implementation paragraph: the block layout, the returns and the constant
rep('E6', '''and replay sweeps check the claimed reads against the input and, on the
second work tape, against each replayed work tape, which `Turing.skipTM`,
`Turing.skipBackTM` and `Turing.clearTM` then erase. -/''', '''and replay sweeps check the claimed reads against the input and, on the
second work tape, against each replayed work tape. That tape is kept there as
one two-cell block per visited cell, rewritten at every record; the last
record's head move is not performed, so the blocks stay contiguous around the
head. Between sweeps `Turing.skipTM` and `Turing.skipBackTM` return the heads
and `Turing.clearTM` erases the blocks. The constant is
`C = 6W + k(2W + 12) + 21 + 15k` with `W = 2k + 4`, for `N`'s `k` work tapes. -/''')
# E5: no run of blank lines
before = len(re.findall(r'\n\n\n+', t))
t = re.sub(r'\n\n\n+', '\n\n', t)
print(f'E5: collapsed {before} blank-line runs')
open(out, 'w', encoding='utf-8').write(t)
