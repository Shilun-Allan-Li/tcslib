"""Build the verified overlay: the brief's overlay plus the new declarations of a (repaired) copy of
the delivered file, without the status paragraph. Asserts that the result differs from the overlay
only by insertions between the replay canonizer's region and the target's docstring.
usage: python3 -I mkoverlay.py <overlay> <repaired file> <out> [last declaration name]"""
import sys, re
ov, rep, out = sys.argv[1], sys.argv[2], sys.argv[3]
last = sys.argv[4] if len(sys.argv) > 4 else None
O = open(ov, encoding='utf-8').read().split('\n')
P = open(rep, encoding='utf-8').read().split('\n')
# the overlay's home ends with ic_table_call's last line "    positive, installs⟩" then a blank line
end_ov = O.index('    positive, installs⟩')
assert O[end_ov + 1] == '' and O[end_ov + 2].startswith('/-- **The interpreter core'), O[end_ov:end_ov + 3]
s = P.index('    positive, installs⟩')
assert P[:s + 1] == O[:end_ov + 1], 'prefix through ic_table_call differs'
t = next(i for i, l in enumerate(P) if l.startswith('/-- **The interpreter core'))
block = P[s + 1:t]          # blank, new declarations..., blank
if last is not None:
    # keep the declarations up to and including `last` (its docstring starts the next cut)
    starts = [i for i, l in enumerate(block) if re.match(r'^private (theorem|def|instance|lemma) ', l)]
    names = [re.match(r'^private (?:theorem|def|instance|lemma) (\S+)', block[i]).group(1) for i in starts]
    k = names.index(last)
    if k + 1 < len(starts):
        j = starts[k + 1]
        while not block[j].startswith('/--'):
            j -= 1
        block = block[:j]
        assert block[-1] == '', block[-3:]
    print('kept', names[:k + 1])
res = O[:end_ov + 1] + block + O[end_ov + 2:]
# sanity: inserted lines only
import difflib
sm = difflib.SequenceMatcher(a=O, b=res, autojunk=False)
ops = [op for op in sm.get_opcodes() if op[0] != 'equal']
assert all(op[0] == 'insert' for op in ops), ops
print('overlay', len(O), 'lines ->', len(res), 'lines; inserted hunks', [(op[1], op[3], op[4]) for op in ops])
open(out, 'w', encoding='utf-8').write('\n'.join(res))
