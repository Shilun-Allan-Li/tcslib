import sys
# usage: reverse.py <base> <head>: undo the B6-F5 edits on <head> (drop the two imports, drop the
# private block from `/-- The forward state` through the blank lines before target 1's docstring,
# drop each "**Fill appendix (B6-F5).**" paragraph and re-attach " -/", restore target 1's body to
# "  sorry") and compare with <base> byte for byte.
base = open(sys.argv[1], encoding='utf-8').read(); h = open(sys.argv[2], encoding='utf-8').read().split('\n')
imports = ['import TCSlib.Complexity.TuringMachine.Build.Contract.Basic', 'import TCSlib.Complexity.TuringMachine.Build.Seam']
assert h[7:9] == imports, h[7:9]
h = h[:7] + h[9:]
a = h.index('/-- The forward state, followed by return and verdict states carrying one Boolean. -/')
b = next(i for i in range(a, len(h)) if h[i].startswith('/-- **The restoring suffix-boundary test**'))
assert h[a - 1] == '' and h[b - 1] == ''
print('private block: head lines', a + 1 + 2, '..', b + 2, '(', b - a, 'lines incl. trailing blanks )')
h = h[:a] + h[b:]
out = []; i = 0; napp = 0
while i < len(h):
    l = h[i]
    if l.startswith('**Fill appendix (B6-F5).**'):
        assert out[-1] == '', out[-1]; out.pop()
        j = i
        while h[j] != ' -/': j += 1
        out[-1] = out[-1] + ' -/'; napp += 1; i = j + 1; continue
    out.append(l); i += 1
txt = '\n'.join(out)
s = txt.index('  refine ⟨rd_State, inferInstance, inferInstance, rd_test')
e = txt.index('\n\n/-- **H5, the ruler device\'s call rows**', s)
txt = txt[:s] + '  sorry' + txt[e:]
print('appendices removed:', napp)
print('REVERSED HEAD == BASE' if txt == base else 'DIFFERENT')
if txt != base:
    import difflib; print('\n'.join(difflib.unified_diff(base.split('\n'), txt.split('\n'), lineterm='')))
