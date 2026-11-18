"""Root-review exception guard. Read-only; no Lean, build, Git or subprocess call.
Only the exact algorithms-only LPN.Defs project import is admitted. This is not
an edit or relaxation of evidence/tools/overlap_step.py's global exclusion.
"""
from pathlib import Path
import ast, hashlib, json, re
WORKTREE = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
AREA = 'TCSlib.Cryptography.Obfuscation.StructuredSeed'
ALLOWED = AREA + '.Reductions.LPN.Defs'
LEAVES = ('lpn_accept_realizes_eq', 'lpn_gap_realizes_eq',
          'lpn_uniform_challenge_reindex', 'lpn_real_seed_reindex',
          'lpn_pre_real_update', 'lpn_pre_uniform_update', 'lpn_real_section',
          'lpn_uniform_section', 'lpn_fix_advice')
TARGETS = tuple(AREA + '.Internal.' + x for x in LEAVES) + (AREA + '.Params.lpn_hop',)
GLOBAL_BAN = "assert not any(l.startswith('import TCSlib.Cryptography.Obfuscation') for l in s.splitlines())"

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def validate(root, packet):
    root, packet = Path(root).resolve(), Path(packet).resolve()
    if root != WORKTREE:
        raise RuntimeError('Use the explicit managed io-sprg worktree')
    index = json.loads((packet / 'overlap/exact-probe-index.json').read_text())
    if tuple(r['name'] for r in index) != TARGETS:
        raise RuntimeError('The reviewed exact ten target names differ')
    global_tool = root / 'evidence/tools/overlap_step.py'
    if GLOBAL_BAN not in global_tool.read_text():
        raise RuntimeError('The independent global owned-import ban is not intact')
    freeze_tool = root / 'evidence/tools/freeze_global.py'
    tree = ast.parse(freeze_tool.read_text())
    nodes = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))
             or isinstance(n, ast.FunctionDef) and n.name == 'parser_functions']
    scope = {}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(freeze_tool), 'exec'), scope)
    parser = scope['parser_functions'](
        root / 'evidence/tools/clash/clash_scan.py', {'strip_code', 'parse_decls'},
        {'KINDS', 'MODS', 'ATTR', 'DECL_RE', 'NAME_RE'})
    cache, contents, hashes = {}, {}, {}
    def children(mod):
        if mod in cache:
            return cache[mod]
        if mod.startswith('TCSlib.'):
            p = root / (mod.replace('.', '/') + '.lean')
        elif mod.startswith('Mathlib.'):
            p = root / '.lake/packages/mathlib' / (mod.replace('.', '/') + '.lean')
        else:
            cache[mod] = []
            return []
        if not p.is_file():
            raise RuntimeError('Missing import source: ' + mod)
        raw = p.read_bytes()
        text = raw.decode()
        code = parser['strip_code'](text)
        contents[mod] = (p, text, code)
        hashes[str(p)] = hashlib.sha256(raw).hexdigest()
        out = []
        for line in code:
            m = re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+)$', line)
            if m:
                out.extend(m[1].split())
        cache[mod] = out
        return out
    seen, todo = set(), [ALLOWED]
    while todo:
        mod = todo.pop()
        if mod not in seen:
            seen.add(mod)
            todo.extend(children(mod))
    prefix = AREA + '.Reductions.LPN'
    forbidden = [prefix + s for s in ('', '.Transport', '.Sections', '.Hop', '.Encoding')]
    forbidden.extend([AREA + '.Security', AREA + '.Targets'])
    bad_modules = sorted(set(forbidden) & seen)
    if bad_modules:
        raise RuntimeError('Target owner/facade entered Defs closure: ' + repr(bad_modules))
    found, code_hits, external_prefix, count, modules = [], [], [], 0, 0
    for mod, (_, text, code) in contents.items():
        if mod.startswith('TCSlib.'):
            modules += 1
            declarations = parser['parse_decls'](text)
            count += len(declarations)
            found.extend({'name': d['full'], 'module': mod, 'line': d['line']}
                         for d in declarations if d['full'] in TARGETS)
            for line_no, line in enumerate(code, 1):
                for leaf in (*LEAVES, 'lpn_hop'):
                    if re.search(r'(?<![\w\u0080-\uffff])' + re.escape(leaf)
                                 + r'(?![\w\u0080-\uffff])', line):
                        code_hits.append({'leaf': leaf, 'module': mod, 'line': line_no})
        elif any(AREA in line for line in code):
            external_prefix.append(mod)
    if found or code_hits or external_prefix:
        raise RuntimeError('Target absence failed: ' + repr((found, code_hits, external_prefix)))
    for path, digest in hashes.items():
        if sha(path) != digest:
            raise RuntimeError('Import source changed during audit: ' + path)
    for row in index:
        template = packet / 'overlap/exact-statements' / Path(row['template']).name
        if sha(template) != row['template_sha256']:
            raise RuntimeError('Reviewed template hash differs: ' + template.name)
        text = template.read_text()
        imports = [line[7:] for line in text.splitlines() if line.startswith('import ')]
        if imports != [ALLOWED, 'Lean.Elab.Tactic.LibrarySearch']:
            raise RuntimeError('Only exact LPN.Defs plus Lean search harness is admitted')
        if text.count('__PROBE_BODY__') != 1 or len(re.findall(r'^example\b', text, re.M)) != 1:
            raise RuntimeError('Expected one exact anonymous goal')
        if re.search(r'\b(?:by|sorry|admit|axiom)\b', '\n'.join(parser['strip_code'](text))):
            raise RuntimeError('Template already has proof/axiom material')
    return {'status': 'SOURCE_IMPORT_AND_TEN_TARGET_ABSENCE_PASS_NOT_LEAN',
            'allowed_project_import': ALLOWED, 'targets': list(TARGETS),
            'closure_nodes': len(seen), 'TCSlib_modules_parsed': modules,
            'TCSlib_declarations_parsed': count, 'forbidden_modules_absent': forbidden,
            'target_declarations_found': found, 'target_leaf_code_occurrences': code_hits,
            'global_overlap_guard_sha256': sha(global_tool),
            'source_sha256': hashes,
            'qualification': 'Lexical current-source import audit. The generated probe also checks '
                'all ten names in its actual Lean environment before searching. No source/object '
                'coherence, owner proof or axiom audit is asserted by this source guard.'}

def lean_guard():
    suffixes = [name.removeprefix(AREA + '.') for name in TARGETS]
    rows = '\n'.join('    ' + json.dumps(x) + (',' if i + 1 < len(suffixes) else '')
                     for i, x in enumerate(suffixes))
    return ('run_cmd do\n  let env ← Lean.getEnv\n'
            '  let prefix := "' + AREA + '."\n  let suffixes : List String := [\n'
            + rows + '\n  ]\n  for suffix in suffixes do\n'
            '    let name := ((prefix ++ suffix).splitOn ".").foldl\n'
            '      (fun n p => Lean.Name.str n p) Lean.Name.anonymous\n'
            '    if env.contains name (skipRealize := false) then\n'
            '      Lean.throwError "LPN_DEFS_TARGET_PRESENT"\n'
            '  IO.println "LPN_DEFS_GUARD_OK_10"\n\n')
