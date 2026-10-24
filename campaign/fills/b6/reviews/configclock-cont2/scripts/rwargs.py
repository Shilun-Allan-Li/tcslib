"""rwargs.py <base> <head> <out json> : collect the arguments of rw/rwa/rewrite/erw/simp/simpa/dsimp/simp_rw/
unfold/delta/show/change/conv/nth_rw in the head lines added by the diff (comment-stripped), and the identifier
tokens in them."""
import difflib, json, re, sys
a = open(sys.argv[1], encoding='utf-8').read().split('\n')
b = open(sys.argv[2], encoding='utf-8').read().split('\n')
added = set()
for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
    if tag in ('replace', 'insert'): added.update(range(j1, j2))
# comment-strip the head, keeping line structure
src = '\n'.join(b); out = []; i = 0; depth = 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
    if depth == 0 and src.startswith('--', i):
        while i < len(src) and src[i] != '\n': i += 1
        continue
    out.append(src[i] if (depth == 0 or src[i] == '\n') else ' '); i += 1
lines = ''.join(out).split('\n')
text = '\n'.join(l if k in added else '' for k, l in enumerate(lines))
TAC = re.compile(r'(?<![\w.])(rw|rwa|rewrite|erw|nth_rw|nth_rewrite|simp_rw|simp only|simp|simpa only|simpa|dsimp only|dsimp|unfold|delta|show|change|conv)(?![\w])')
def bracket(s, k):
    assert s[k] == '['
    d = 0
    for j in range(k, len(s)):
        if s[j] == '[': d += 1
        elif s[j] == ']':
            d -= 1
            if d == 0: return s[k + 1:j], j
    return s[k + 1:], len(s)
ID = re.compile(r"(?<![\w.'])([A-Za-z_][\w.'₀-₉ₐ-ₜ!?]*)")
KW = {'at', 'using', 'with', 'by', 'fun', 'from', 'if', 'then', 'else', 'Type', 'Prop', 'show', 'this', 'in',
      'let', 'have', 'match', 'Sort', 'do', 'only'}
calls = []
for m in TAC.finditer(text):
    tac = m.group(1); k = m.end(); ln = text.count('\n', 0, m.start()) + 1
    rest = text[k:]
    st = rest.lstrip(' ')
    off = k + (len(rest) - len(st))
    if tac in ('unfold', 'delta'):
        arg = re.match(r"[^\n]*", st).group(0)
    elif tac in ('show', 'change'):
        # the term up to ' from ' / ' by ' / ':= ' or end of line, continuing onto more-indented lines
        seg = []; pos = off
        first = text[pos:].split('\n')[0]
        seg.append(first)
        indent = len(lines[ln - 1]) - len(lines[ln - 1].lstrip())
        nl = ln
        while nl < len(lines) and lines[nl].strip() and (len(lines[nl]) - len(lines[nl].lstrip())) > indent + 2 and nl in added:
            seg.append(lines[nl]); nl += 1
        arg = ' '.join(seg)
        arg = re.split(r'\s(from|by)\s|:=', arg)[0]
    elif st.startswith('['):
        arg, _ = bracket(text, off)
    else:
        nxt = re.match(r"[^\n]*", st).group(0)
        if tac.startswith(('simp', 'dsimp', 'simpa')) and '[' in nxt.split(' at ')[0].split(' using ')[0]:
            arg, _ = bracket(text, text.index('[', off))
        else:
            arg = '' if tac.startswith(('simp', 'dsimp', 'simpa')) else nxt
    toks = sorted({t.rstrip('.') for t in ID.findall(arg.replace('←', ' ')) if t not in KW})
    calls.append({'line': ln, 'tac': tac, 'arg': ' '.join(arg.split())[:300], 'ids': toks})
json.dump(calls, open(sys.argv[3], 'w', encoding='utf-8'), ensure_ascii=False, indent=0)
print('calls', len(calls), 'distinct identifiers', len({t for c in calls for t in c['ids']}))
from collections import Counter
print(Counter(c['tac'] for c in calls))
print('bare simp/simpa/dsimp (no lemma list):', [(c['line'], c['tac']) for c in calls if c['tac'].startswith(('simp', 'dsimp', 'simpa')) and not c['arg']])
