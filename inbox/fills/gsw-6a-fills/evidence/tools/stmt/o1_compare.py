"""o1_compare.py <repo> <base> <o1-head>: byte comparison of the block moved by O1.
Old: TreeNCAC.lean lines 172-350 at <base> (section header through combine_size).
New: the same section of FormulaArith/Combinators.lean at <o1-head> (from the section header up to,
not including, the new readers `balanced_nil`/`balanced_singleton`).
The renames of O1 are applied to the old block first, as whole-word token substitutions:
combine -> TreeCircuit.balanced, combine_eval -> TreeCircuit.balanced_eval,
combine_maxFanin -> TreeCircuit.maxFanin_balanced_le, combine_depth -> TreeCircuit.depth_balanced_le,
combine_size -> TreeCircuit.size_balanced_le, and `private ` dropped on those five declarations.
Prints (1) the unified diff of the raw bytes, (2) the unified diff with all runs of whitespace (newlines
included) collapsed, token by token, and classifies every hunk."""
import sys, subprocess, re, difflib
repo, base, head = sys.argv[1:4]
show = lambda rev, p: subprocess.run(['git', '-C', repo, 'show', f'{rev}:{p}'], capture_output=True,
                                     check=True).stdout.decode('utf8')
old = show(base, 'TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean').split('\n')[171:350]
newsrc = show(head, 'TCSlib/Complexity/CircuitComplexity/FormulaArith/Combinators.lean').split('\n')
a = next(i for i, l in enumerate(newsrc) if l.startswith('/-! ### Simulating an unbounded gate'))
b = next(i for i, l in enumerate(newsrc) if 'The balanced tree over no children' in l)
new = newsrc[a:b]
while new and new[-1] == '': new.pop()
while old and old[-1] == '': old.pop()
ren = [('combine_eval', 'TreeCircuit.balanced_eval'), ('combine_maxFanin', 'TreeCircuit.maxFanin_balanced_le'),
       ('combine_depth', 'TreeCircuit.depth_balanced_le'), ('combine_size', 'TreeCircuit.size_balanced_le'),
       ('combine', 'TreeCircuit.balanced')]
o = '\n'.join(old)
for x, y in ren:
    o = re.sub(r'(?<![\w.])' + re.escape(x) + r'(?![\w])', y, o)
for nm in ['def TreeCircuit.balanced', 'theorem TreeCircuit.balanced_eval', 'theorem TreeCircuit.maxFanin_balanced_le',
           'theorem TreeCircuit.depth_balanced_le', 'theorem TreeCircuit.size_balanced_le']:
    o = o.replace('private ' + nm, nm)
oldr = o.split('\n')
print('== old block: base', base, 'TreeNCAC.lean:172-350 (%d lines, renames applied)' % len(old))
print('== new block: head', head, 'Combinators.lean:%d-%d (%d lines)' % (a + 1, b, len(new)))
print('== (1) raw unified diff')
raw = list(difflib.unified_diff(oldr, new, 'old(renamed)', 'new', n=0, lineterm=''))
print('\n'.join(raw))
print('== (2) whitespace-insensitive diff (token stream)')
tok = lambda s: re.findall(r'\S+', s)
ot, nt = tok('\n'.join(oldr)), tok('\n'.join(new))
sm = difflib.SequenceMatcher(a=ot, b=nt, autojunk=False)
hunks = [op for op in sm.get_opcodes() if op[0] != 'equal']
for tag, i1, i2, j1, j2 in hunks:
    print(f'-- {tag}: old {" ".join(ot[i1:i2])!r}\n   new {" ".join(nt[j1:j2])!r}')
print('== hunks: raw', sum(1 for l in raw if l.startswith('@@')), 'whitespace-insensitive', len(hunks))
