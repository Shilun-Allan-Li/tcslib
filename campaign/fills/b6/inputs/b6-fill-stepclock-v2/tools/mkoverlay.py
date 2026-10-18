"""Build the pre-ship overlay of Build/StepClock.lean (B6 fill, batch F1: the step clock).

Usage: python3 -I mkoverlay.py <repo-root> <home.lean.txt> <headline.lean.txt> <out.lean>

Two asserted edits on the issue-tree file, nothing else:
  1. the home: the blank line between `Turing.Cfg.Stopped`'s body and the docstring of
     `Turing.exists_stepClockTMVia` receives the home block;
  2. the headline's body (`  sorry`, the line after its statement's `:= by`) is replaced by the
     prescribed glue.
The script checks that the result minus the two inserted blocks is the issue-tree file.
"""
import sys, hashlib

root, home_p, glue_p, out_p = sys.argv[1:5]
src_p = f'{root}/TCSlib/Complexity/TuringMachine/Build/StepClock.lean'
src = open(src_p, encoding='utf-8').read()
home = open(home_p, encoding='utf-8').read()
glue = open(glue_p, encoding='utf-8').read()
lines = src.split('\n')

# edit 1: the home line
doc = "/-- **H3's clock, the step-clocked runner** (joint statement with C1, whose draft"
idx = [i for i, l in enumerate(lines) if l == doc]
assert len(idx) == 1, ('headline docstring anchor', idx)
h = idx[0] - 1
assert lines[h] == '', ('home line not blank', h + 1, lines[h])
assert lines[h - 1] == '  c.state = none ∨ ∃ s, c.state = some s ∧ stopAt s = true', \
    ('Cfg.Stopped body', lines[h - 1])
home_line = h + 1  # 1-based

# edit 2: the headline's body
decl = 'theorem exists_stepClockTMVia {k : ℕ} {Γ S : Type} [Fintype S] [DecidableEq S]'
d = [i for i, l in enumerate(lines) if l == decl]
assert len(d) == 1, ('headline declaration anchor', d)
j = d[0]
while not lines[j].endswith(':= by'):
    j += 1
    assert j - d[0] < 60, 'statement end not found'
assert lines[j + 1] == '  sorry', ('headline body', lines[j + 1])
assert lines[j + 2] == '', ('headline body end', lines[j + 2])
body_line = j + 2  # 1-based line of the `sorry`

home_lines = home.rstrip('\n').split('\n')
glue_lines = glue.rstrip('\n').split('\n')
new = lines[:h] + [''] + home_lines + [''] + lines[h + 1:j + 1] + glue_lines + lines[j + 2:]
out = '\n'.join(new)

# reverse check: removing the two blocks gives back the issue-tree file
back = new[:h] + [''] + new[h + 1 + len(home_lines) + 1:]
k = back.index(decl)
m = k
while not back[m].endswith(':= by'):
    m += 1
assert back[m + 1:m + 1 + len(glue_lines)] == glue_lines
back = back[:m + 1] + ['  sorry'] + back[m + 1 + len(glue_lines):]
assert '\n'.join(back) == src, 'reverse check failed'

open(out_p, 'w', encoding='utf-8').write(out)
sha = lambda b: hashlib.sha256(b.encode('utf-8')).hexdigest()
print(f'issue-tree StepClock.lean: {len(lines)} lines, sha256 {sha(src)}')
print(f'home: line {home_line} (blank), {len(home_lines)} lines inserted')
print(f'headline body: line {body_line} (`  sorry`) replaced by {len(glue_lines)} lines')
print(f'overlay: {len(new)} lines, sha256 {sha(out)}')
