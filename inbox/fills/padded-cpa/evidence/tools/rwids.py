# Collect identifiers passed to rw/rwa/erw/simp/simp only/simp_rw/simpa/dsimp/unfold in the
# added lines of the padded-cpa patch series, per file; write evidence/seal/RwIds*.lean.
import re, subprocess, collections
F = '/home/user/fill'; BASE = '4a09f3993eb9344fc5714610e41ab141a0144db8'
diff = subprocess.run(['git', '-C', F, 'diff', '-U0', BASE + '..fill/padded-cpa'],
                      capture_output=True, text=True).stdout
added = collections.defaultdict(list); cur = None
for l in diff.splitlines():
    if l.startswith('+++ '): cur = l[6:]; continue
    if l.startswith('+') and not l.startswith('+++') and cur: added[cur].append(l[1:])
kw = re.compile(r'\b(rw|rwa|erw|simp_rw|simp only|simpa only|simpa|simp|dsimp only|dsimp)\s*(\[)')
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
    for m in re.finditer(r'\bunfold\s+([\w. ]+)', text):
        for t in m.group(1).split(): ids[f].add(t)
ctx = {
  'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean':
    ('RwIdsChallengeSim', 'TCSlib.Cryptography.Composability.ChallengeSim',
     'Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp'),
  'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean':
    ('RwIdsRecordHandler', 'TCSlib.Cryptography.Composability.ChallengeSim',
     'Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games'),
  'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean':
    ('RwIdsOracleSecurity', 'TCSlib.Cryptography.Composability',
     'Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp'),
}
tsv = open(F + '/evidence/logs/rwids-files.tsv', 'w')
for f, (out, ns, opens) in ctx.items():
    lst = sorted(ids[f])
    for x in lst: tsv.write(f + '\t' + x + '\n')
    body = '''import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command

/-! Explicit readings of the padded-cpa fill in `%s`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace %s
open %s

def idsToCheck : List String := [%s]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let n := s.toName
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
    open(F + '/evidence/seal/' + out + '.lean', 'w').write(body)
    print(f, len(lst))
