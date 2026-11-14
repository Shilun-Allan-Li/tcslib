"""Prepare reproducible Rule-10 probes; never invokes Lean.

Run as python3 -I prepare_seals.py inventory|prepare|scan --help.
Snapshots and probes are outside TCSlib; each must be checked separately through
scripts/lean_check_tree.sh, in the emitted order. Existing attempts are immutable.
Design reference: Gate06 build_seals.py and its V3 harness notes at the issue base.
No source or proof is copied from those files; the actual-Name lookup and serialized
request approach follows their reviewed design.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def save(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        raise RuntimeError(f'refusing to replace existing evidence: {path}')
    path.write_bytes(raw if isinstance(raw, bytes) else raw.encode())


def lean_string(value):
    return json.dumps(value, ensure_ascii=False)


def blank_comments(text):
    out = list(text)
    depth, i = 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            n = 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            n = 2
        elif not depth and text.startswith('--', i):
            n = text.find('\n', i)
            n = len(text) - i if n == -1 else n - i
        elif depth:
            n = 1
        else:
            i += 1
            continue
        for k in range(i, i + n):
            if out[k] != '\n':
                out[k] = ' '
        i += n
    if depth:
        raise RuntimeError('unclosed comment')
    return ''.join(out)


def imports(raw):
    result = []
    for line in blank_comments(raw.decode()).splitlines():
        if line.strip().startswith('import '):
            result.extend(line.strip().split()[1:])
    return result


def read_source(root, module, revision):
    path = module.replace('.', '/') + '.lean'
    if revision:
        p = subprocess.run(['git', '-C', str(root), 'show', revision + ':' + path],
                           capture_output=True)
        return None if p.returncode else p.stdout
    p = root / path
    return p.read_bytes() if p.exists() else None


def closure(root, module, revision):
    seen = set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        raw = read_source(root, m, revision)
        if raw is None:
            raise RuntimeError(f'missing source for closure module: {m}')
        for dep in imports(raw):
            if dep.startswith('TCSlib.'):
                visit(dep)
    visit(module)
    return sorted(seen - {module})


def make_inventory(args):
    root, evidence = Path(args.root), Path(args.evidence)
    if len(args.targets) != 1:
        raise RuntimeError('use one target per phase: unchanged-name snapshots cannot safely be imported together')
    dest = evidence / 'seals' / args.phase
    if dest.exists():
        raise RuntimeError(f'phase already exists: {dest}')
    records, queue = [], []
    for index, module in enumerate(args.targets):
        raw = read_source(root, module, args.revision)
        if raw is None:
            records.append(dict(target=module, absent_at_revision=True,
                                revision=args.revision))
            continue
        probe_module = f'LamportEvidence.Seals.{args.phase}.Snapshot{index}'
        probe_path = probe_module.replace('.', '/')
        deps = closure(root, module, args.revision)
        record = dict(target=module, revision=args.revision or 'WORKING_TREE',
                      snapshot_module=probe_module, snapshot_path=probe_path,
                      source_sha256=sha(raw), closure=deps,
                      closure_source_sha256={d: sha(read_source(root, d, args.revision)) for d in deps},
                      raw_source='raw-sources/' + module.replace('.', '/') + '.lean')
        records.append(record)
        queue.append(probe_path)
        save(dest / record['raw_source'], raw)
        save(root / (probe_path + '.lean'), raw)
    active = [x for x in records if not x.get('absent_at_revision')]
    source = 'import Lean\n' + ''.join('import ' + r['snapshot_module'] + '\n' for r in active)
    source += '\nset_option maxHeartbeats 0\nopen Lean Meta Elab Command\n\n'
    for record in active:
        payload = '\n'.join(record['closure'])
        source += f'''run_cmd do
  let target : String := {lean_string(record['target'])}
  let ownHome : String := {lean_string(record['snapshot_module'])}
  let payload : String := {lean_string(payload)}
  let homes := if payload.isEmpty then [] else payload.splitOn "\\n"
  let env ← getEnv
  unless env.header.moduleNames.any (fun m => m.toString == ownHome) do
    throwError "LAMP-INVENTORY missing own snapshot {{ownHome}}"
  for home in homes do
    unless env.header.moduleNames.any (fun m => m.toString == home) do
      throwError "LAMP-INVENTORY missing closure module {{home}}"
  let mut rows : Array String := #[]
  let mut axs : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!.toString
    unless home == ownHome || homes.contains home do continue
    let status ← liftCoreM <| getReducibilityStatus n
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let instanceFlag := isInstanceCore env n
    rows := rows.push s!"LAMP-CATALOG\\t{{target}}\\t{{n.toString}}\\t{{home}}\\t{{ci.isDefinition}}\\t{{instanceFlag}}\\t{{matcher}}\\t{{repr status}}"
    if home == ownHome then
      let aa ← liftCoreM <| collectAxioms n
      let aa := aa.qsort (fun a b => a.toString < b.toString)
      axs := axs.push s!"LAMP-AXIOMS\\t{{target}}\\t{{n.toString}}\\t{{aa.toList}}"
  for row in rows.qsort (· < ·) do logInfo m!"{{row}}"
  for row in axs.qsort (· < ·) do logInfo m!"{{row}}"
  logInfo m!"LAMP-INVENTORY-END\\t{{target}}\\t{{rows.size}}\\t{{axs.size}}\\t{{homes.length}}"

'''
    inventory_module = f'LamportEvidence.Seals.{args.phase}.Inventory'
    inventory_path = inventory_module.replace('.', '/')
    queue.append(inventory_path)
    save(root / (inventory_path + '.lean'), source)
    save(dest / 'Inventory.lean', source)
    save(dest / 'manifest.json', json.dumps(dict(phase=args.phase, records=records,
          inventory_module=inventory_module, inventory_sha256=sha(source.encode()),
          policy=dict(instances_excluded=True, reducible_abbreviations_excluded=True,
                      private_definitions_included=True, generated_matchers_included=True,
                      projections_included=True)), indent=2) + '\n')
    save(dest / 'inventory-order.txt', '\n'.join(queue) + '\n')
    print(dest / 'inventory-order.txt')


def parse_catalog(path):
    rows, ends, exact_closures = {}, {}, {}
    for line in path.read_text().splitlines():
        if line.startswith('LAMP-CATALOG\t'):
            fields = line.split('\t')
            if len(fields) != 8:
                raise RuntimeError('malformed catalog row: ' + line)
            _, target, spelling, home, isdef, inst, matcher, status = fields
            status = status.rsplit('.', 1)[-1]
            if status not in ('reducible', 'semireducible', 'irreducible'):
                raise RuntimeError('unknown reducibility status: ' + status)
            rows.setdefault(target, []).append(dict(spelling=spelling, home=home,
                is_definition=isdef == 'true', instance=inst == 'true',
                matcher=matcher == 'true', status=status))
        if line.startswith('LAMP-CLOSURE-EXACT\t'):
            _, target, count = line.split('\t')
            if target in exact_closures:
                raise RuntimeError('duplicate exact closure marker: ' + target)
            exact_closures[target] = int(count)
        if line.startswith('LAMP-INVENTORY-END\t'):
            _, target, count, axs, deps = line.split('\t')
            if target in ends:
                raise RuntimeError('duplicate inventory end: ' + target)
            ends[target] = (int(count), int(axs), int(deps))
    for target, values in ends.items():
        if exact_closures.get(target) != values[2]:
            raise RuntimeError('missing/wrong exact TCSlib closure marker: ' + target)
        if len(rows.get(target, [])) != values[0]:
            raise RuntimeError('inventory row count differs: ' + target)
    return rows, ends


def seal_command(label, rows, verify=False):
    payload = '\n'.join(r['spelling'] + '\t' + r['home'] for r in rows)
    operation = 'EOF' if verify else 'INSTALL'
    source = '\nset_option maxHeartbeats 0\nrun_cmd do\n'
    source += '  Lean.Elab.Command.liftCoreM do\n'
    source += rf'''    let label : String := {lean_string(label)}
    let payload : String := {lean_string(payload)}
    let lines := if payload.isEmpty then [] else payload.splitOn "\n"
    unless lines.length == {len(rows)} do throwError "LAMP-HARNESS bad serialized count"
    let mut wanted : Std.HashSet String := {{}}
    for row in lines do
      let [spelling, _home] := row.splitOn "\t" | throwError "LAMP-HARNESS malformed row"
      wanted := wanted.insert spelling
    let env ← Lean.getEnv
    let mut catalog : Std.HashMap String (Array Lean.Name) := {{}}
    for (n, _) in env.constants.map₁.toList do
      let spelling := n.toString
      unless wanted.contains spelling do continue
      let some mi := env.getModuleIdxFor? n | continue
      unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
      catalog := catalog.insert spelling (((catalog[spelling]?).getD #[]).push n)
'''
    if not verify:
        source += '''    let attr ← Lean.ofExcept <| Lean.getAttributeImpl (← Lean.getEnv) `irreducible
'''
    source += rf'''    let mut count : Nat := 0
    for row in lines do
      let [spelling, home] := row.splitOn "\t" | throwError "LAMP-HARNESS malformed row"
      let ns := (catalog[spelling]?).getD #[]
      unless ns.size == 1 do throwError "LAMP-HARNESS absent/ambiguous {{spelling}}"
      let n := ns[0]!
      let some mi := env.getModuleIdxFor? n | throwError "LAMP-HARNESS no home {{spelling}}"
      unless env.header.moduleNames[mi.toNat]!.toString == home do
        throwError "LAMP-HARNESS wrong home {{spelling}}"
      let some ci := env.find? n | throwError "LAMP-HARNESS no constant {{spelling}}"
      unless ci.isDefinition do throwError "LAMP-HARNESS not definition {{spelling}}"
'''
    if not verify:
        source += '''      let before ← Lean.getReducibilityStatus n
      unless before == .irreducible do
        Lean.withExporting (isExporting := false) do
          attr.add n Lean.Syntax.missing .local
'''
    source += rf'''      let after ← Lean.getReducibilityStatus n
      unless after == .irreducible do throwError "LAMP-HARNESS unsealed {{spelling}}"
      Lean.logInfo m!"LAMP-SEAL-NAME\t{{label}}\t{operation}\t{{spelling}}\t{{home}}"
      count := count + 1
    unless count == {len(rows)} do throwError "LAMP-HARNESS wrong verified count"
    Lean.logInfo m!"LAMP-SEAL-{operation}\t{{label}}\t{{count}}"

'''
    return source


def instrument(raw, label, rows):
    lines = raw.decode().splitlines(keepends=True)
    clean = blank_comments(raw.decode()).splitlines(keepends=True)
    positions = [i for i, line in enumerate(clean) if line.strip().startswith('import ')]
    if not positions:
        raise RuntimeError('unsupported source without imports')
    insert = positions[-1] + 1
    # The full original source is preserved byte-for-byte around insertions.
    prefix = ''.join(lines[:insert])
    if not prefix.endswith('\n'):
        prefix += '\n'
    result = 'import Lean\n' + prefix + seal_command(label, rows)
    body_start = len(result.splitlines()) + 1
    result += ''.join(lines[insert:])
    if not result.endswith('\n'):
        result += '\n'
    result += seal_command(label, rows, verify=True)
    mapping = [dict(original_start=1, original_end=insert, generated_start=2,
                    generated_end=insert + 1)]
    if insert < len(lines):
        mapping.append(dict(original_start=insert + 1, original_end=len(lines),
                            generated_start=body_start,
                            generated_end=body_start + len(lines) - insert - 1))
    return result, mapping


def make_seals(args):
    root, evidence = Path(args.root), Path(args.evidence)
    dest = evidence / 'seals' / args.phase
    manifest = json.loads((dest / 'manifest.json').read_text())
    log = Path(args.catalog_log)
    if re.search(r'\.lean:\d+:\d+: error:', log.read_text()):
        raise RuntimeError('inventory has Lean errors')
    catalog, ends = parse_catalog(log)
    probes, queue = [], []
    for index, record in enumerate(manifest['records']):
        if record.get('absent_at_revision'):
            continue
        target = record['target']
        if target not in ends:
            raise RuntimeError('incomplete inventory: ' + target)
        rows = [r for r in catalog[target] if r['home'] != record['snapshot_module']
                and r['is_definition'] and not r['instance'] and r['status'] != 'Lean.ReducibilityStatus.reducible'
                and r['status'] != 'reducible']
        rows.sort(key=lambda r: r['spelling'])
        for mode in ('A', 'B'):
            selected = [r for r in rows if mode == 'B' or r['spelling'] != 'Complexity.PolyExpr.eval']
            label = f'{args.phase}_{index}_{mode}'
            mod = f'LamportEvidence.Seals.{args.phase}.Seal{index}{mode}'
            path = mod.replace('.', '/')
            raw = (dest / record['raw_source']).read_bytes()
            assert sha(raw) == record['source_sha256']
            source, source_map = instrument(raw, label, selected)
            save(root / (path + '.lean'), source)
            save(dest / 'probes' / (label + '.lean'), source)
            request = dict(target=target, label=label, module=mod, mode=mode,
                  source_sha256=sha(raw), probe_sha256=sha(source.encode()),
                  original_line_map=source_map, requests=selected)
            save(dest / 'requests' / (label + '.json'), json.dumps(request, indent=2) + '\n')
            probes.append(request)
            queue.append(path)
    # One ordinary foreign-definition control for each mode, plus a reader positive.
    ordinary = next((r for r in manifest['records'] if not r.get('absent_at_revision') and
                     any(x['spelling'] in ('Complexity.NUPPT.inArg', 'TCSlib.Cryptography.Games.ProbComp.expect') for x in catalog[r['target']])), None)
    if ordinary:
        controls_header = 'import Lean\n' + ''.join('import ' + x + '\n' for x in imports(
            (dest / ordinary['raw_source']).read_bytes()))
        negative = 'example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by\n  rfl\n'
        positive = 'example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by\n  exact Complexity.NUPPT.inArg_eq z\n'
        sensitivity_symbol = 'Complexity.NUPPT.inArg'
        if not any(r['spelling'] == sensitivity_symbol for r in catalog[ordinary['target']]):
            sensitivity_symbol = 'TCSlib.Cryptography.Games.ProbComp.expect'
            negative = 'example (x : ℝ) : TCSlib.Cryptography.Games.ProbComp.expect (.pure x) (fun y => y) = x := by\n  rfl\n'
            positive = 'example (x : ℝ) : TCSlib.Cryptography.Games.ProbComp.expect (.pure x) (fun y => y) = x := by\n  exact TCSlib.Cryptography.Games.ProbComp.expect_pure x (fun y => y)\n'
        full = [r for r in catalog[ordinary['target']] if r['home'] != ordinary['snapshot_module']
                and r['is_definition'] and not r['instance'] and 'reducible' != r['status']
                and r['status'] != 'Lean.ReducibilityStatus.reducible']
        for mode in ('A', 'B'):
            selected = sorted([r for r in full if mode == 'B' or r['spelling'] != 'Complexity.PolyExpr.eval'],key=lambda x:x['spelling'])
            for kind, body, expected in [('Unsealed', negative, 0), ('Negative', negative, 1), ('Reader', positive, 0)]:
                label=f'{args.phase}_Control{mode}{kind}'
                mod=f'LamportEvidence.Seals.{args.phase}.Control{mode}{kind}'
                source=controls_header+'\nset_option maxHeartbeats 0\n'
                if kind != 'Unsealed': source += seal_command(label, selected)
                proof_line=len(source.splitlines())+2
                source+=body
                if kind != 'Unsealed': source += seal_command(label, selected, verify=True)
                save(root/(mod.replace('.','/')+'.lean'),source)
                save(dest/'controls'/(label+'.lean'),source)
                probes.append(dict(label=label,module=mod,control=True,sensitivity_symbol=sensitivity_symbol,expected_errors=expected,
                    expected_error_line=proof_line if expected else None,probe_sha256=sha(source.encode()),requests=selected if kind!='Unsealed' else []))
                queue.append(mod.replace('.','/'))
    save(dest/'seal-manifest.json',json.dumps(dict(inventory_log_sha256=sha(log.read_bytes()),probes=probes),indent=2)+'\n')
    save(dest/'seal-order.txt','\n'.join(queue)+'\n')
    print(dest/'seal-order.txt')


def scan(args):
    root, evidence=Path(args.root),Path(args.evidence)
    catalog,_=parse_catalog(Path(args.catalog_log))
    manifest=json.loads((evidence/'seals'/args.phase/'manifest.json').read_text())
    homes={r['snapshot_module']:r['target'] for r in manifest['records'] if not r.get('absent_at_revision')}
    for rows in catalog.values():
        for row in rows:
            row['home']=homes.get(row['home'],row['home'])
    allrows={r['spelling']:r for values in catalog.values() for r in values}
    results=[]
    for target in args.targets:
        raw=read_source(root,target,None)
        if raw is None: continue
        code=blank_comments(raw.decode())
        pattern=re.compile(r'\b(?:simp(?:_all)?(?:\s+only)?|simpa(?:\s+only)?|rw|rwa|erw|dsimp)\s*\[([^\]]*)\]|\b(?:unfold|delta)\s+([^\n;]+)',re.M)
        for match in pattern.finditer(code):
            region=match.group(1) or match.group(2)
            for name in re.findall(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*",region):
                candidates=[r for n,r in allrows.items() if n==name or n.endswith('.'+name)]
                foreign=[r for r in candidates if r['home']!=target and r['is_definition']]
                results.append(dict(target=target,line=code.count('\n',0,match.start())+1,
                    operation=match.group(0).split()[0],identifier=name,candidates=candidates,
                    foreign_definition_candidates=foreign))
    save(evidence/'seals'/args.phase/'explicit-unfold-scan.json',json.dumps(results,indent=2)+'\n')
    print(f'{len(results)} token readings; {sum(bool(r["foreign_definition_candidates"]) for r in results)} require foreign-definition review. Ambiguous suffixes are candidates, not proven violations.')


parser=argparse.ArgumentParser(description=__doc__)
sub=parser.add_subparsers(dest='action',required=True)
for action in ('inventory','prepare','scan'):
    p=sub.add_parser(action)
    p.add_argument('--root',required=True);p.add_argument('--evidence',required=True)
    p.add_argument('--phase',required=True)
    if action=='inventory':p.add_argument('--revision')
    if action in ('inventory','scan'):p.add_argument('targets',nargs='+')
    if action in ('prepare','scan'):p.add_argument('--catalog-log',required=True)
args=parser.parse_args()
if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*',args.phase):raise RuntimeError('phase must be a Lean identifier')
{'inventory':make_inventory,'prepare':make_seals,'scan':scan}[args.action](args)
