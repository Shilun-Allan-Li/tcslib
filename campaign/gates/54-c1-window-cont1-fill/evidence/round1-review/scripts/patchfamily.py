"""Normalize the four interval-patch definitions: drop the name, the docstring and the alphabet
binder; rename every bound identifier in order of first appearance; compare token streams."""
import re, sys, os
root = sys.argv[1]
items = [
  ('Build/StepClock.lean', 'wordPatch'),
  ('Build/CounterLoop.lean', 'counterPatch'),
  ('Build/Catalog.lean', 'catalogTape'),
  ('Build/InputWindow.lean', 'iw_patch'),
]
TOK = re.compile(r'[A-Za-z_Ͱ-Ͽᴀ-ᶿ][A-Za-z0-9_.\'Ͱ-Ͽ₀-ₜ]*|\d+|ℤ|ℕ|→|≤|∧|<|:=|=>|[(){}\[\]:+\-*,]|\S')
KEEP = {'def','private','fun','if','then','else','Option','List','Type','Type*','FinTM.bufferTape',
        'length','ℤ','ℕ','→','≤','∧','<',':=','=>','(',')','{','}','[',']',':','+','-','*',',','q'}
for f, name in items:
    p = os.path.join(root, 'TCSlib/Complexity/TuringMachine', f)
    L = open(p, encoding='utf-8').read().split('\n')
    i = next(k for k, l in enumerate(L) if re.match(r'\s*(private\s+)?def\s+' + re.escape(name) + r'\b', l))
    j = i
    while j + 1 < len(L) and L[j + 1].strip() and not L[j + 1].lstrip().startswith(('/--', 'theorem', 'lemma', 'private', 'def')):
        j += 1
    code = '\n'.join(L[i:j + 1])
    print(f'== {f}:{i+1}-{j+1} `{name}` ({len(code)} chars, {j-i+1} code lines)')
    print(code)
    s = code
    s = re.sub(r'\{(Γ|Symbol)\s*:\s*Type\*?\}\s*', '', s)          # alphabet binder
    s = re.sub(r'\b(Γ|Symbol|Bool)\b', 'A', s)                      # alphabet
    s = re.sub(r'\(q\s*:\s*ℤ\)\s*:\s*Option A\s*:=', ': ℤ → Option A := fun q =>', s)  # pointwise form
    toks = TOK.findall(s)
    toks = toks[toks.index(name) + 1:]                               # drop `private def name`
    ren, out = {}, []
    for t in toks:
        if t.endswith('.length') and t[:-7] and t[:-7] not in KEEP:
            b = t[:-7]; ren.setdefault(b, 'x%d' % (len(ren) + 1)); out.append(ren[b] + '.length'); continue
        if re.match(r'^[A-Za-z_]', t) and t not in KEEP and t not in ('A', 'Option'):
            ren.setdefault(t, 'x%d' % (len(ren) + 1)); out.append(ren[t]); continue
        out.append(t)
    norm = ' '.join(out)
    print('   normalized:', norm)
    print('   renaming:', ren)
    items[items.index((f, name))] = (f, name, norm)
base = items[0][2]
print()
for f, name, norm in items:
    print(f'{name:14s} identical to wordPatch after normalization: {norm == base}')
