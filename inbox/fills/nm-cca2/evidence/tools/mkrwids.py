#!/usr/bin/env python3
"""Explicit-unfold scan of the nm-cca2 fill: every identifier that the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold`, `delta` or `show … from`,
per file, resolved in the file's namespace with its `open`s by a Lean module. A definition may be
passed only when it is the file's own."""
import re, subprocess, collections
F = '/workspace/fill'; BASE = 'b96ab3ccc1915497ea3138df499eec00b6581db0'
diff = subprocess.run(['git', '-C', F, 'diff', '-U0', BASE + '..fill/nm-cca2'],
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
D = 'TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/'
BO = 'Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games'
NS = 'TCSlib.Cryptography.Composability.NMCCA2'
ctx = {
  D + 'Indistinguishability/Readers.lean': ('RwIdsReaders', NS, BO, ''),
  D + 'Indistinguishability/Forward.lean': ('RwIdsForward', NS, BO, ''),
  D + 'Indistinguishability/Decrypt.lean': ('RwIdsDecrypt', NS, BO,
     'open AdaptiveCPA (acDin acDout acDin_zero acDout_zero)'),
  D + 'Indistinguishability/Encrypt.lean': ('RwIdsEncrypt', NS, BO,
     'open AdaptiveCPA (acDin acDout acDout_zero)'),
  D + 'Indistinguishability.lean': ('RwIdsOwned', 'TCSlib.Cryptography.Composability.FixedLengthPKScheme',
     BO + ' AdaptiveCPA NMCCA2 ProbComp ChallengeSim', ''),
}
tsv = open('/workspace/payload/evidence/logs/rwids-files.tsv', 'w')
for f, (out, ns, opens, extra) in ctx.items():
    lst = sorted(ids[f])
    for x in lst: tsv.write(f + '\t' + x + '\n')
    body = '''import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
open Lean Elab Command

/-! Explicit readings of the nm-cca2 fill in `%s`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace %s
open %s
%s

def idsToCheck : List String := [%s]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else s
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
''' % (f, ns, opens, extra, ','.join('"%s"' % x for x in lst), ns)
    open(F + '/scratch/seal/' + out + '.lean', 'w').write(body)
    print(f, len(lst))
