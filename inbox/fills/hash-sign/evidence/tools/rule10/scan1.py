"""scan1.py <scan_explicit.py> <worktree> <touched.json> <out.json> <probe.lean> <file>...
Phase 1 of the final explicit-reader scan: runs the archived lexer (`inventory`, the reviewed
continuation-list lexer of gates/10-efficiency/verification.zip) over each file, attaches each item
to its declaration (touched.json spans), computes the namespace/open context, and writes a native
kinds probe resolving every candidate full name of every head (and of the definition behind every
`.eq_N`/`.eq_def`/`.eq_unfold` head)."""
import sys, json, re, importlib.util
from pathlib import Path
lexer_path, wt, touched_path, out_path, probe_path = sys.argv[1:6]
files = sys.argv[6:]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('archived_scan_explicit', lexer_path)
lex = importlib.util.module_from_spec(spec); spec.loader.exec_module(lex)
touched = json.load(open(touched_path))['files']
EQN = re.compile(r'^(.*)\.(eq_\d+|eq_def|eq_unfold)$')
items, cands = [], set()
for f in files:
    raw = (Path(wt) / f).read_text(encoding='utf-8')
    code = lex.blank(raw).split('\n')
    module = f[:-5].replace('/', '.')
    # namespace / open context per line (top-level commands; sections scope opens)
    ctx = []; ns = []; opens = [[]]; scopes = []
    for i, l in enumerate(code):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m:
            parts = m.group(1).split('.'); ns.extend(parts); scopes.append(('ns', len(parts))); opens.append([])
        elif re.match(r'^(noncomputable\s+)?section\b', l):
            scopes.append(('sec', 0)); opens.append([])
        elif re.match(r'^end\b', l):
            if scopes:
                kind, k = scopes.pop(); opens.pop()
                if kind == 'ns': del ns[len(ns) - k:]
        else:
            m = re.match(r'^open\s+(?:scoped\s+)?(.*?)(\s+in\s*)?$', l)
            if m and not m.group(2):
                names = [x for x in m.group(1).split() if not x.startswith('(') and x not in ('hiding', 'renaming')]
                opens[-1].extend(names)
        ctx.append(('.'.join(ns), [o for s in opens for o in s]))
    decls = touched[f]['declarations']
    for row in lex.inventory(raw):
        line = row['line']
        owner = [d for d in decls if d['start'] <= line <= d['end']]
        nspace, op = ctx[line - 1]
        # tactic-local `open X in` within the owning declaration
        local_opens = []
        if owner:
            for j in range(owner[0]['start'] - 1, min(owner[0]['end'], len(code))):
                for m in re.finditer(r'\bopen\s+([A-Za-z_][\w.]*)(?:\s+[A-Za-z_][\w.]*)*\s+in\b', code[j]):
                    local_opens.append(m.group(1))
        head = row['head']
        target = EQN.match(head)
        heads = [head] + ([target.group(1)] if target else [])
        names = []
        for h in heads:
            if h.startswith('_root_.'): names.append(h[7:]); continue
            parts = nspace.split('.') if nspace else []
            for k in range(len(parts), -1, -1):
                pre = '.'.join(parts[:k])
                names.append((pre + '.' if pre else '') + h)
                names.append('_private.' + module + '.0.' + (pre + '.' if pre else '') + h)
            for o in op + local_opens:
                names.append(o + '.' + h)
                for k in range(len(parts), 0, -1):
                    names.append('.'.join(parts[:k]) + '.' + o + '.' + h)
        names = list(dict.fromkeys(names))
        cands.update(names)
        items.append(dict(file=f, module=module, line=line, tactic=row['tactic'], item=' '.join(row['item'].split()),
                          head=head, eqn_target=target.group(1) if target else None, namespace=nspace,
                          opens=op + local_opens, candidates=names,
                          declaration=owner[0]['name'] if owner else None,
                          declaration_status=owner[0]['status'] if owner else 'OUTSIDE',
                          touched=owner[0]['touched'] if owner else None))
json.dump({'items': items, 'count': len(items)}, open(out_path, 'w'), indent=1)
lines = ['import Lean', *('import ' + f[:-5].replace('/', '.') for f in files), '', 'set_option maxHeartbeats 0', 'open Lean Elab Command', '',
         'def candsPayload : String := ' + json.dumps('\n'.join(sorted(cands)), ensure_ascii=False)]
lines += ['', 'run_cmd do', '  let cands := candsPayload.splitOn "\\n"', '  let env ← getEnv',
 '  let mut byStr : Std.HashMap String Name := {}',
 '  for (n, _) in env.constants.toList do',
 '    byStr := byStr.insert n.toString n',
 '  for s in cands do',
 '    let some n := byStr[s]? | continue',
 '    let some ci := env.find? n | continue',
 '    let home := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!.toString',
 '    let kind := match ci with',
 '      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"',
 '      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"',
 '      | .inductInfo _ => "inductive" | .axiomInfo _ => "axiom" | .quotInfo _ => "quotient"',
 '    let abbrevFlag := match ci with',
 '      | .defnInfo d => match d.hints with | .abbrev => true | _ => false',
 '      | _ => false',
 '    let status := match Lean.getReducibilityStatusCore env n with',
 '      | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"',
 '    IO.println ("EXPLICIT_KIND " ++ (Json.mkObj [("spelling", toJson s), ("name", toJson n.toString), ("home", toJson home),',
 '      ("kind", toJson kind), ("abbrev", toJson abbrevFlag), ("status", toJson status),',
 '      ("projection", toJson (env.isProjectionFn n)), ("instance", toJson (Lean.Meta.isInstanceCore env n))]).compress)',
 '  IO.println s!"EXPLICIT_KIND_DONE {cands.length}"', '']
Path(probe_path).write_text('\n'.join(lines), encoding='utf-8')
print('items', len(items), 'candidates', len(cands))
