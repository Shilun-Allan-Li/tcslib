#!/usr/bin/env python3
"""Explicit-unfold scan of the nm-sim fill: every identifier that the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold`, `delta` or `show … from`,
per file, resolved in the file's namespace with the file's own `open` lines by a Lean module. A
definition may be passed only when it is the file's own."""
import re, subprocess, collections, sys
sys.path.insert(0, '/workspace/simtools')
from nmsim_files import FILES
F = '/workspace/sim'; BASE = '262d6e9ae526c82eb68fe5a6169156bd1504e6d8'
diff = subprocess.run(['git', '-C', F, 'diff', '-U0', BASE + '..fill/nm-sim'],
                      capture_output=True, text=True).stdout
added = collections.defaultdict(list); cur = None
for l in diff.splitlines():
    if l.startswith('+++ '): cur = l[6:]; continue
    if l.startswith('+') and not l.startswith('+++') and cur: added[cur].append(l[1:])
kw = re.compile(r'\b(rw|rwa|erw|simp_rw|simp only|simpa only|simpa|simp|dsimp only|dsimp|nth_rw \d+)\s*(\[)')
ids = collections.defaultdict(set)
for f, lines in added.items():
    text = '\n'.join(re.sub(r'--.*', '', x) for x in lines)
    for m in kw.finditer(text):
        i = m.end(); depth = 1; j = i
        while j < len(text) and depth:
            depth += {'[': 1, ']': -1}.get(text[j], 0); j += 1
        inner = text[i:j - 1]
        parts, d, buf = [], 0, ''
        for ch in inner:
            if ch in '([{⟨': d += 1
            if ch in ')]}⟩': d -= 1
            if ch == ',' and d == 0: parts.append(buf); buf = ''
            else: buf += ch
        parts.append(buf)
        for p in parts:
            p = p.strip().lstrip('←').strip()
            if p.startswith('show ') or p.startswith('('):
                mm = re.search(r'\bfrom\s+([\w.\']+)', p)
                if mm: ids[f].add(mm.group(1))
                continue
            mm = re.match(r"[\w.'₀-₉]+", p)
            if mm: ids[f].add(mm.group(0))
    for m in re.finditer(r'\b(unfold|delta)\s+([\w.\' ]+)', text):
        for t in m.group(2).split(): ids[f].add(t)
tsv = open('/workspace/simpay/evidence/logs/rwids-files.tsv', 'w')
for name, f in FILES.items():
    if name == 'Base': continue
    src = open(F + '/' + f).read()
    m = re.search(r'\nnamespace (\S+)', src); ns = m.group(1)
    if name == 'Owned': ns = 'TCSlib.Cryptography.Composability.FixedLengthPKScheme'
    ol, keep = [], False
    for l in src.splitlines():
        if l.startswith('open '): keep = True; ol.append(l); continue
        if keep and l.startswith('  '): ol.append(l); continue
        keep = False
    opens = '\n'.join(ol)
    lst = sorted(ids[f])
    for x in lst: tsv.write(f + '\t' + x + '\n')
    body = '''import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Explicit readings of the nm-sim fill in `%s`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace %s
%s

def idsToCheck : List String := [%s]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else
      if s.startsWith "M." then "MsgSampler." ++ (s.drop 2) else
      if s.startsWith "samp." then "Complexity.NUPPT." ++ (s.drop 5) else s
    let n := s'.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    let env ← getEnv
    let modOf (c : Name) : String :=
      ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!.toString).getD "?"
    if cands.isEmpty then IO.println s!"{s}: (unresolved: local hypothesis or private)"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some _ => "other"
        | none => "?"
      IO.println s!"{s}: {c}: {k} ({modOf c})"

end %s
''' % (f, ns, opens, ','.join('"%s"' % x for x in lst), ns)
    open(F + '/scratch/seal/RwIds' + name + '.lean', 'w').write(body)
    print(name, ns, len(lst))
