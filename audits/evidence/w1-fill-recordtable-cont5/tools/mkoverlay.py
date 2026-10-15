"""Build the pre-ship overlay of Build/RecordTable.lean (w1 record tables, continuation 5).

Usage: python3 -I mkoverlay.py <repo-root> <home.lean.txt> <row18body.lean.txt> <out.lean>

Two asserted edits on the tip file, nothing else:
  1. the prescribed home: the blank line between the end of `exists_recordTemplateTM`'s
     proof and the docstring of `exists_recordInitTM` receives the home block;
  2. row 18's body (`  sorry`, the first line after its statement's `:= by`) is replaced by
     the pre-ship skeleton.
The script checks that the result minus the two inserted blocks is the tip file.
"""
import sys, hashlib

root, home_p, body_p, out_p = sys.argv[1:5]
src_p = f'{root}/TCSlib/Complexity/TuringMachine/Build/RecordTable.lean'
src = open(src_p, encoding='utf-8').read()
home = open(home_p, encoding='utf-8').read()
body = open(body_p, encoding='utf-8').read()
lines = src.split('\n')

# edit 1: the home line
doc = '/-- **R8.7, the initial record** (design §12.8a §3, §12.8b). For a start state'
idx = [i for i, l in enumerate(lines) if l == doc]
assert len(idx) == 1, ('row-18 docstring anchor', idx)
h = idx[0] - 1
assert lines[h] == '', ('home line not blank', h + 1, lines[h])
assert lines[h - 1] == '  · rfl', ('row 17 proof end', lines[h - 1])
home_line = h + 1  # 1-based

# edit 2: row 18's body
decl = 'theorem exists_recordInitTM (k : ℕ) {Q T : Type} [Fintype Q] [DecidableEq Q] [Fintype T]'
d = [i for i, l in enumerate(lines) if l == decl]
assert len(d) == 1, ('row-18 declaration anchor', d)
j = d[0]
while not lines[j].endswith(':= by'):
    j += 1
    assert j - d[0] < 40, 'statement end not found'
assert lines[j + 1] == '  sorry', ('row-18 body', lines[j + 1])
assert lines[j + 2] == '', ('row-18 body end', lines[j + 2])
body_line = j + 2  # 1-based line of the `sorry`

home_lines = home.rstrip('\n').split('\n')
body_lines = body.rstrip('\n').split('\n')
new = lines[:h] + [''] + home_lines + [''] + lines[h + 1:j + 1] + body_lines + lines[j + 2:]
out = '\n'.join(new)

# reverse check: removing the two blocks gives back the tip file
back = new[:h] + [''] + new[h + 1 + len(home_lines) + 1:]
k = back.index(decl)
m = k
while not back[m].endswith(':= by'):
    m += 1
assert back[m + 1:m + 1 + len(body_lines)] == body_lines
back = back[:m + 1] + ['  sorry'] + back[m + 1 + len(body_lines):]
assert '\n'.join(back) == src, 'reverse check failed'

open(out_p, 'w', encoding='utf-8').write(out)
sha = lambda b: hashlib.sha256(b.encode('utf-8')).hexdigest()
print(f'tip RecordTable.lean: {len(lines)} lines, sha256 {sha(src)}')
print(f'home: tip line {home_line} (blank), {len(home_lines)} lines inserted')
print(f'row 18 body: tip line {body_line} (`  sorry`) replaced by {len(body_lines)} lines')
print(f'overlay: {len(new)} lines, sha256 {sha(out)}')
