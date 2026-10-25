import sys, re, json
# usage: rwargs.py <head file> <worker.diff> <out json>
src = open(sys.argv[1], encoding='utf-8').read()
diff = open(sys.argv[2], encoding='utf-8').read().split('\n')
added = set(); ln = 0
for l in diff:
    m = re.match(r'^@@ -\d+(?:,\d+)? \+(\d+)', l)
    if m: ln = int(m.group(1)); continue
    if l.startswith('+++') or l.startswith('---'): continue
    if l.startswith('+'): added.add(ln); ln += 1
    elif l.startswith('-'): pass
    else: ln += 1
# strip comments/docstrings, keep positions
out = []; i = 0; depth = 0; n = len(src)
while i < n:
    if src.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
    if depth > 0 and src.startswith('-/', i): depth -= 1; out.append('  '); i += 2; continue
    if depth > 0: out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
    if src.startswith('--', i):
        j = src.find('\n', i); j = n if j < 0 else j
        out.append(' ' * (j - i)); i = j; continue
    out.append(src[i]); i += 1
code = ''.join(out)
assert len(code) == len(src)
lineof = lambda pos: code.count('\n', 0, pos) + 1
TAC = re.compile(r'(?<![\w.])(rw|rwa|rewrite|erw|simp_rw|simp only|simp|simpa only|simpa|dsimp only|dsimp|unfold|delta|show|change|simp_all|field_simp|norm_num|simp_arith)(?![\w.!?\'])')
IDENT = re.compile(r"(?<![\w.'])([A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏][\w.'À-ɏͰ-Ͽἀ-῿⁰-₟℀-⅏!?₀-₉]*)")
KEYW = {'at','with','using','by','fun','if','then','else','show','from','have','let','in','only','this','match','do','true','false','by_cases','calc','Type','Prop','Sort','sorry','exact','rfl','decide','omega','simp','intro','obtain','rcases','refine','apply','constructor','left','right','at','ne','le','lt'}
calls = []
for m in TAC.finditer(code):
    pos = m.start(); L = lineof(pos)
    if L not in added: continue
    tac = m.group(1)
    rest = code[m.end():]
    args = ''; kind = 'list'
    if tac in ('unfold', 'delta'):
        args = rest.split('\n', 1)[0]; args = re.split(r'\bat\b', args)[0]; kind = 'unfold'
    elif tac in ('show', 'change'):
        # the term up to ' from ', ' by ', ' := ', ' at ' or end of line, or the matching close
        line = rest.split('\n', 1)[0]
        depthp = 0; endj = len(line)
        for j, ch in enumerate(line):
            if ch in '([{⟨': depthp += 1
            elif ch in ')]}⟩':
                if depthp == 0: endj = j; break
                depthp -= 1
            elif depthp == 0 and (line.startswith(' from', j) or line.startswith(' by ', j) or line.startswith(' by\n', j) or line.startswith(' at ', j) or line.startswith(',', j)):
                endj = j; break
        args = line[:endj]; kind = 'term'
    else:
        s = rest.lstrip(' ')
        if s.startswith('['):
            d = 0
            for j, ch in enumerate(s):
                if ch == '[': d += 1
                elif ch == ']':
                    d -= 1
                    if d == 0: args = s[1:j]; break
            kind = 'list'
        else:
            args = ''; kind = 'bare'
    ids = [x for x in IDENT.findall(args) if x not in KEYW and not x[0].isdigit()]
    calls.append({'line': L, 'tac': tac, 'kind': kind, 'args': ' '.join(args.split())[:400], 'ids': ids})
json.dump(calls, open(sys.argv[3], 'w'), ensure_ascii=False, indent=0)
from collections import Counter
print('calls on added lines:', len(calls), Counter(c['tac'] for c in calls))
print('identifier occurrences:', sum(len(c['ids']) for c in calls), '; distinct:', len({i for c in calls for i in c['ids']}))
print('bare (default simp set) calls:', [(c['line'], c['tac']) for c in calls if c['kind'] == 'bare' and c['tac'] in ('simp','simpa','dsimp','simp_all','field_simp','norm_num')][:80])
