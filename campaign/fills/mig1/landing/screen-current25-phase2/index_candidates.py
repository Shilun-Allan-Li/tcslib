"""Index three exact v3 populations; compare reused base/previous outputs with fresh phase2 head, without tiling."""
from pathlib import Path
import ast, collections, hashlib, json, re, sys

p = Path(__file__).resolve().parent
paths = (p / 'population.txt').read_text().splitlines()
source = (p / 'copy-text-screen-v3.py.txt').read_text()
tree = ast.parse(source)
nodes = [n for n in tree.body if
         isinstance(n, ast.FunctionDef) and n.name in ['scopes', 'qualify', 'body'] or
         isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id in ['DECL', 'SCOPE'] for t in n.targets)]
ns = {'re': re, 'sys': sys}
exec(compile(ast.Module(body=nodes, type_ignores=[]), '<reviewed-v3-index-functions>', 'exec'), ns)

def stripped_with_map(src):
    out, offsets = [], []
    i = depth = 0
    while i < len(src):
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            i = len(src) if j < 0 else j
            continue
        out.append(src[i]); offsets.append(i); i += 1
    return ''.join(out), offsets

indexes = {}
all_declarations = {}
base_counts = collections.Counter(Path(path).name for path in paths)
for label in ['base', 'previous-head', 'head']:
    index, all_decls = {}, []
    for path in paths:
        raw = (p/'inputs'/label/(path+'.txt')).read_text()
        t, offsets = stripped_with_map(raw)
        matches = list(ns['DECL'].finditer(t))
        events = ns['scopes'](path, t)
        found = []
        for i, m in enumerate(matches):
            end = matches[i+1].start() if i+1 < len(matches) else len(t)
            bd = re.sub(r'\s+', '', ns['body'](t[m.start():end]))
            namespace = [n for o, n in events if o <= m.start()][-1]
            start_raw = offsets[m.start()]
            end_raw = offsets[end] if end < len(offsets) else len(raw)
            row = {'path': path, 'name': m.group(3), 'qualified': ns['qualify'](namespace, m.group(3)),
                   'kind': 'proof' if m.group(2) in ('theorem', 'lemma') else 'term',
                   'declaration_kind': m.group(2), 'private': 'private' in m.group(1).split(),
                   'start_line': raw.count('\n', 0, start_raw)+1,
                   'end_line': raw.count('\n', 0, end_raw)+1,
                   'raw_start': start_raw, 'raw_end': end_raw,
                   'body_chars': len(bd), 'body_sha256': hashlib.sha256(bd.encode()).hexdigest(),
                   'screened': len(bd) >= 60}
            all_decls.append(row)
            if row['screened']: found.append(row)
        short = collections.Counter(row['name'] for row in found)
        qualified = collections.Counter(row['qualified'] for row in found)
        seen = collections.Counter()
        for row in found:
            if short[row['name']] == 1:
                name = row['name']
            elif qualified[row['qualified']] == 1:
                name = row['qualified']
            else:
                seen[row['qualified']] += 1
                name = row['qualified'] + '#' + str(seen[row['qualified']])
            filename = Path(path).name if base_counts[Path(path).name] == 1 else path
            key = filename + '::' + name
            assert key not in index, key
            row = dict(row, screen_label=key)
            index[key] = row
    indexes[label] = index
    all_declarations[label] = all_decls
    (p/(label+'-declarations.json')).write_text(json.dumps(all_decls, indent=2)+'\n')
    (p/(label+'-screen-index.json')).write_text(json.dumps(index, indent=2)+'\n')

if not (p/'head.json').exists():
    print(json.dumps({'indexed': {label: len(index) for label,index in indexes.items()},
                      'candidate_index_pending': 'fresh phase2 head still running'}))
    raise SystemExit(0)

pattern = re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%$')
screens = {}; summaries = {}
for label in ['base', 'previous-head', 'head']:
    text = (p/(label+'.out')).read_text()
    m = re.match(r'declarations screened: (\d+); copy pairs .*: (\d+); reproduced text: ([\d,]+) chars', text)
    assert m
    summary = {'declarations': int(m[1]), 'directed_pairs': int(m[2]), 'reproduced_chars': int(m[3].replace(',',''))}
    assert summary['declarations'] == len(indexes[label])
    rows = {}
    for line in text.splitlines()[1:]:
        m = pattern.match(line); assert m, line
        a,b,shared,length,percent = m.groups()
        target,original = indexes[label][a], indexes[label][b]
        assert target['kind'] == original['kind']
        row = {'target':a,'source':b,'shared_chars':int(shared),'source_body_chars':int(length),
               'rounded_percent':int(percent),'kind':target['kind'],
               'cross_file':target['path']!=original['path'],
               'target_path':target['path'],'source_path':original['path'],
               'target_line':target['start_line'],'source_line':original['start_line']}
        assert row['source_body_chars']==original['body_chars'] and (a,b) not in rows
        rows[(a,b)]=row
    assert len(rows)==summary['directed_pairs']
    summary['unordered_pairs']=len({tuple(sorted(key)) for key in rows})
    summary['kind_location']=dict(collections.Counter(row['kind']+'/'+('cross-file' if row['cross_file'] else 'in-file') for row in rows.values()))
    summaries[label]=summary; screens[label]=rows
    (p/(label+'-all-candidates.json')).write_text(json.dumps(list(rows.values()),indent=2)+'\n')
for label,earlier,prefix in [('vs-base','base','B'),('vs-previous-head','previous-head','P')]:
    new=[dict(row,id=f'{prefix}{i:03d}') for i,row in enumerate((row for key,row in screens['head'].items() if key not in screens[earlier]),1)]
    gone=[row for key,row in screens[earlier].items() if key not in screens['head']]
    changed=[{'head':row,'earlier':screens[earlier][key]} for key,row in screens['head'].items()
             if key in screens[earlier] and (row['shared_chars'],row['source_body_chars']) !=
             (screens[earlier][key]['shared_chars'],screens[earlier][key]['source_body_chars'])]
    for name,rows in [('new-all',new),('new-cross-file',[r for r in new if r['cross_file']]),
                      ('new-in-file',[r for r in new if not r['cross_file']]),('gone-all',gone),('changed-metrics',changed)]:
        (p/(label+'-'+name+'.json')).write_text(json.dumps(rows,indent=2)+'\n')
    summaries[label]={'new':len(new),'gone':len(gone),'existing_with_changed_metrics':len(changed),
        'new_kind_location':dict(collections.Counter(row['kind']+'/'+('cross-file' if row['cross_file'] else 'in-file') for row in new))}
(p/'candidate-summary.json').write_text(json.dumps(summaries,indent=2)+'\n')
print(json.dumps(summaries,indent=2))
