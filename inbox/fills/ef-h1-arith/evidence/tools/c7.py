# c7.py <repo> <base> <head> <file> <allowed-inserted-lines-file>: the head file must equal the base file
# plus exactly the allowed inserted lines (in order); prints the verdict, then runs a one-character control.
import subprocess, sys, difflib
repo, base, head, f, allowed = sys.argv[1:6]
def show(rev): return subprocess.run(['git','-C',repo,'show',f'{rev}:{f}'],capture_output=True,text=True).stdout.split('\n')
def check(b, h, allow):
    sm = difflib.SequenceMatcher(a=b, b=h, autojunk=False)
    ins, bad = [], []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal': continue
        if op == 'insert': ins += h[j1:j2]
        else: bad.append((op, b[i1:i2], h[j1:j2]))
    return bad, ins == allow, ins
b, h = show(base), show(head)
allow = open(allowed).read().split('\n')[:-1]
bad, okins, ins = check(b, h, allow)
print(f"{f}: base {len(b)} lines, head {len(h)} lines; non-insert differences: {len(bad)}; inserted {len(ins)} lines; inserted == allowed: {okins}")
# control: alter one character of one base line in the head copy -> exactly one difference
h2 = list(h); k = next(i for i, l in enumerate(h2) if l.startswith('* `Factoring`')); h2[k] = h2[k].replace('F', 'G', 1)
bad2, _, _ = check(b, h2, allow)
print(f"control (one character altered at head line {k+1}): non-insert differences: {len(bad2)}")
