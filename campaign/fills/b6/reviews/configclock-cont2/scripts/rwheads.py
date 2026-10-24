"""rwheads.py <calls json> <head module> <out .lean> : rule heads of each rw/simp/dsimp/unfold call (the first
identifier of each top-level comma-separated element), and a classification probe (the module + #rv_classify)."""
import json, re, sys
calls = json.load(open(sys.argv[1], encoding='utf-8'))
ID = re.compile(r"(?<![\w.'])([A-Za-z_][\w.'₀-₉ₐ-ₜ!?]*)")
def split_top(s):
    out, d, cur = [], 0, ''
    for ch in s:
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        if ch == ',' and d == 0: out.append(cur); cur = ''
        else: cur += ch
    out.append(cur); return [x.strip() for x in out if x.strip()]
heads = []
for c in calls:
    if c['tac'] in ('show', 'change'): continue
    elems = c['arg'].split() if c['tac'] in ('unfold', 'delta') else split_top(c['arg'])
    for e in elems:
        e = e.replace('←', ' ').strip()
        e = e.lstrip('(').strip()
        m = ID.match(e)
        if m: heads.append((c['line'], c['tac'], m.group(1).rstrip('.'), e[:80]))
        else: heads.append((c['line'], c['tac'], None, e[:80]))
json.dump(heads, open(sys.argv[1].replace('.json', '-heads.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=0)
names = sorted({h[2] for h in heads if h[2]} | {t for c in calls for t in c['ids']})
TACW = {'_', 'exact', 'omega', 'show', 'simp', 'rw', 'positivity', 'push_cast', 'ring', 'tauto', 'decide',
        'linarith', 'nlinarith', 'norm_num', 'intro', 'refine', 'apply'}
NAME = re.compile(r"^[A-Za-z][\w'₀-₉]*(\.[A-Za-z][\w'₀-₉?!]*)*$")
dropped = [n for n in names if n in TACW or not NAME.match(n)]
names = [n for n in names if n not in TACW and NAME.match(n)]
print('dropped (tactic words, `_`, field indices):', dropped)
src = open(sys.argv[2], encoding='utf-8').read()
k = src.rindex('end Turing')
kit = r'''
open Lean Elab Command in
elab "#rv_classify " ids:ident* : command => do
  for id in ids do
    let r ← liftTermElabM (do
      try pure (some (← resolveGlobalConst id)) catch _ => pure none)
    match r with
    | none => logInfo m!"CLS {id.getId} | - | local or unresolved | -"
    | some ns =>
      for n in ns do
        let env ← getEnv
        let kind := match env.find? n with
          | some (.thmInfo _) => "thm" | some (.defnInfo _) => "def" | some (.inductInfo _) => "induct"
          | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "rec" | some (.axiomInfo _) => "axiom"
          | some (.opaqueInfo _) => "opaque" | some (.quotInfo _) => "quot" | none => "?"
        let md := match env.getModuleIdxFor? n with
          | some i => (env.header.moduleNames[i]?).getD `none
          | none => `this
        logInfo m!"CLS {id.getId} | {n} | {kind} | {md}"

'''
body = '#rv_classify ' + ' '.join(names) + '\n\n'
open(sys.argv[3], 'w', encoding='utf-8').write(src[:k] + kit + body + src[k:])
print('heads', len(heads), 'names to classify', len(names))
