"""Build the pre-ship overlay of Build/WindowRun.lean (B6 fill, batch F2: the windowed runner).

Usage: python3 -I mkoverlay.py <repo-root> <homeA.lean.txt> <loopbody.lean.txt>
                               <homeB.lean.txt> <runnerbody.lean.txt> <out.lean>

Four asserted edits on the issue-tree file, nothing else:
  A. home A: the blank line between `/-! ### The machines -/` and the docstring of
     `Turing.exists_windowLoopTM` receives home block A;
  1. the loop's body (`  sorry`) is replaced by the pre-ship skeleton;
  B. home B: the blank line between the loop's body and the docstring of
     `Turing.exists_windowRunnerTM` receives home block B;
  2. the runner's body (`  sorry`) is replaced by the pre-ship skeleton.
The script checks that removing the four blocks gives back the issue-tree file.
"""
import sys, hashlib

root, ha_p, lb_p, hb_p, rb_p, out_p = sys.argv[1:7]
src_p = f'{root}/TCSlib/Complexity/TuringMachine/Build/WindowRun.lean'
src = open(src_p, encoding='utf-8').read()
read = lambda p: open(p, encoding='utf-8').read().rstrip('\n').split('\n')
homeA, loopb, homeB, runb = read(ha_p), read(lb_p), read(hb_p), read(rb_p)
L = src.split('\n')

def one(pred, what):
    idx = [i for i, l in enumerate(L) if pred(l)]
    assert len(idx) == 1, (what, idx)
    return idx[0]

def body_of(decl_line, what):
    d = one(lambda l: l == decl_line, what)
    j = d
    while not L[j].endswith(':= by'):
        j += 1
        assert j - d < 60, (what, 'statement end not found')
    assert L[j + 1] == '  sorry', (what, 'body', L[j + 1])
    assert L[j + 2] == '', (what, 'body end', L[j + 2])
    return j + 1  # 0-based index of the `  sorry`

sec = one(lambda l: l == '/-! ### The machines -/', 'machines section')
hA = sec + 1
assert L[hA] == '', ('home A not blank', L[hA])
assert L[hA + 1].startswith("/-- **H3's loop: the unclocked windowed round loop.**"), L[hA + 1]
loop_sorry = body_of('theorem exists_windowLoopTM (M : FinTM Bool) {T : Type} [Fintype T] '
                     '[DecidableEq T]', 'loop')
hB = loop_sorry + 1
assert L[hB] == '', ('home B not blank', L[hB])
assert L[hB + 1].startswith('/-- **H3, the windowed runner**'), L[hB + 1]
run_sorry = body_of('theorem exists_windowRunnerTM (M : FinTM Bool) {T : Type} [Fintype T] '
                    '[DecidableEq T]', 'runner')
assert hA < loop_sorry < hB < run_sorry

new = (L[:hA] + [''] + homeA + [''] + L[hA + 1:loop_sorry] + loopb + [''] + homeB + [''] +
       L[hB + 1:run_sorry] + runb + L[run_sorry + 1:])
out = '\n'.join(new)

# reverse check
back = []
i = 0
blocks = [(hA, homeA), (loop_sorry, loopb), (hB, homeB), (run_sorry, runb)]
rebuilt = (L[:hA] + [''] + L[hA + 1:loop_sorry] + ['  sorry'] + [''] + L[hB + 1:run_sorry] +
           ['  sorry'] + L[run_sorry + 1:])
assert '\n'.join(rebuilt) == src, 'reverse check failed'
pos = 0
for blk in [homeA, loopb, homeB, runb]:
    k = out.find('\n'.join(blk), pos)
    assert k >= 0, 'block not found in order'
    pos = k + 1

open(out_p, 'w', encoding='utf-8').write(out)
sha = lambda b: hashlib.sha256(b.encode('utf-8')).hexdigest()
print(f'issue-tree WindowRun.lean: {len(L)} lines, sha256 {sha(src)}')
print(f'home A: line {hA + 1} (blank), {len(homeA)} lines inserted')
print(f'loop body: line {loop_sorry + 1} (`  sorry`) replaced by {len(loopb)} lines')
print(f'home B: line {hB + 1} (blank), {len(homeB)} lines inserted')
print(f'runner body: line {run_sorry + 1} (`  sorry`) replaced by {len(runb)} lines')
print(f'overlay: {len(new)} lines, sha256 {sha(out)}')
