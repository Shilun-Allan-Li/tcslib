"""Read-only local-ref API candidate enumeration; never executes repository payloads."""
from pathlib import Path
import collections, datetime, hashlib, json, re, subprocess

OUT = Path(__file__).resolve().parent
ROOT = Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')

def git(*args, check=True):
    result = subprocess.run(['git', *args], cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    if check and result.returncode:
        raise RuntimeError((args, result.returncode, result.stderr.decode()))
    return result

def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

raw = git('for-each-ref', '--format=%(refname)').stdout
(OUT / 'refs-names.txt').write_bytes(raw)
names = raw.decode().splitlines()
oids = git('rev-parse', *[n + '^{commit}' for n in names]).stdout.decode().splitlines()
assert len(names) == len(oids)
commits = sorted(set(oids))
trees = git('rev-parse', *[c + '^{tree}' for c in commits]).stdout.decode().splitlines()
assert len(commits) == len(trees)
checked = subprocess.run(['git', 'cat-file', '--batch-check=%(objectname) %(objecttype)'],
                         cwd=ROOT, input=('\n'.join(commits + trees) + '\n').encode(),
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
(OUT / 'commit-tree-object-check.txt').write_bytes(checked)
assert all(line.endswith(b' commit') for line in checked.splitlines()[:len(commits)])
assert all(line.endswith(b' tree') for line in checked.splitlines()[len(commits):])
refs = [dict(ref=n, commit=c) for n, c in zip(names, oids)]
commit_rows = []
source_populations = {}
blob_paths = collections.defaultdict(set)
for c, tree in zip(commits, trees):
    tc = git('rev-parse', c + ':TCSlib', check=False)
    source_tree = tc.stdout.decode().strip() if tc.returncode == 0 else None
    if source_tree and source_tree not in source_populations:
        rows = []
        for entry in git('ls-tree', '-rz', source_tree).stdout.split(b'\0'):
            if not entry:
                continue
            info, path = entry.split(b'\t', 1)
            mode, kind, oid = info.decode().split()
            path = 'TCSlib/' + path.decode()
            if kind == 'blob' and path.endswith('.lean'):
                rows.append(dict(path=path, blob=oid))
                blob_paths[oid].add(path)
        source_populations[source_tree] = rows
    commit_rows.append(dict(commit=c, tree=tree, TCSlib_tree=source_tree,
                            lean_sources=len(source_populations.get(source_tree, []))))
dump('refs.json', refs)
dump('commits.json', commit_rows)
dump('source-tree-populations.json', source_populations)
(OUT / 'worktrees-raw.txt').write_bytes(git('worktree', 'list', '--porcelain').stdout)

requested = ['pairDiagTM_spaceUsed', 'incFixedTM_spaceUsed',
             'exists_first_entry_of_fixed', 'redirectTM_spaceUsedByTape']
name_re = re.compile('|'.join(re.escape(n) for n in requested))
decl_re = re.compile(r'^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
                     r'(theorem|lemma|def|abbrev)\s+([^\s(:]+)', re.M)

def header_end(text):
    """Find the declaration's body delimiter outside nested delimiters/comments/strings."""
    stack = []; block = 0; string = False; i = 0
    while i < len(text):
        two = text[i:i+2]; ch = text[i]
        if block:
            if two == '/-': block += 1; i += 2; continue
            if two == '-/': block -= 1; i += 2; continue
            i += 1; continue
        if string:
            if ch == '\\': i += 2; continue
            if ch == '"': string = False
            i += 1; continue
        if two == '/-': block = 1; i += 2; continue
        if two == '--':
            end = text.find('\n', i); i = len(text) if end < 0 else end + 1; continue
        if ch == '"': string = True; i += 1; continue
        if ch in '([{': stack.append(ch)
        elif ch in ')]}' and stack: stack.pop()
        elif two == ':=' and not stack: return i
        i += 1
    return len(text)

names_hits = []
candidates = []
groups = {}
blobs = []
process = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
                           stdin=subprocess.PIPE, stdout=subprocess.PIPE)
for oid, paths in sorted(blob_paths.items()):
    process.stdin.write((oid + '\n').encode()); process.stdin.flush()
    meta = process.stdout.readline().decode().split()
    assert meta[0] == oid and meta[1] == 'blob'
    size = int(meta[2]); data = process.stdout.read(size); assert len(data) == size
    assert process.stdout.read(1) == b'\n'
    assert hashlib.sha1(b'blob ' + str(size).encode() + b'\0' + data).hexdigest() == oid
    blobs.append(dict(blob=oid, bytes=size, sha256=hashlib.sha256(data).hexdigest(), paths=sorted(paths)))
    text = data.decode('utf-8', errors='replace')
    for lineno, line in enumerate(text.splitlines(), 1):
        matches = name_re.findall(line)
        if matches:
            names_hits.append(dict(blob=oid, paths=sorted(paths), line=lineno, text=line, names=matches))
    if not any(t in text for t in ['pairDiagTM', 'incFixedTM', 'first_entry',
                                    'exists_first_halt', 'zero_tapes_eq_zero', 'redirectTM']):
        continue
    decls = list(decl_re.finditer(text))
    for j, match in enumerate(decls):
        end = decls[j+1].start() if j+1 < len(decls) else len(text)
        block = text[match.start():end]
        header = block[:header_end(block)]
        reasons = []
        if any(n in match.group(2) for n in requested): reasons.append('requested-name declaration')
        if ('pairDiagTM' in block or 'incFixedTM' in block) and 'spaceUsed' in block:
            reasons.append('canonical-machine zero/resource shape')
        if 'spaceUsed_zero_tapes_eq_zero' in match.group(2): reasons.append('published generic zero-tapes fact')
        if ('first_entry' in match.group(2) or 'exists_first_halt' in match.group(2)):
            reasons.append('first-entry or first-halt declaration')
        if 'stop' in header and 'runFrom' in header and ('step' in header or '∃ t' in header):
            reasons.append('absorbing-stop/run shape')
        if 'redirectTM' in block and 'spaceUsedByTape' in block:
            reasons.append('redirect per-tape shape')
        if not reasons:
            continue
        normalized = re.sub(r'\s+', ' ', header).strip()
        key = hashlib.sha256(normalized.encode()).hexdigest()
        if key not in groups:
            groups[key] = dict(name=match.group(2), kind=match.group(1), header=header,
                               normalized_header=normalized, reasons=set(), occurrences=[])
            (OUT / 'candidates').mkdir(exist_ok=True)
            (OUT / 'candidates' / (key + '.lean.txt')).write_text(block)
        groups[key]['reasons'].update(reasons)
        row = dict(blob=oid, paths=sorted(paths), line=text[:match.start()].count('\n')+1,
                   name=match.group(2), kind=match.group(1), header_group=key, reasons=reasons)
        candidates.append(row); groups[key]['occurrences'].append(row)
process.stdin.close(); assert process.wait() == 0
dump('blob-population.json', blobs)
dump('name-hits.json', names_hits)
dump('shape-candidates.json', candidates)
for group in groups.values(): group['reasons'] = sorted(group['reasons'])
dump('header-groups.json', groups)
summary = dict(captured_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               ref_count=len(refs), unique_commits=len(commits), unique_source_trees=len(source_populations),
               unique_lean_blobs=len(blobs), unique_source_paths=len(set(p for ps in blob_paths.values() for p in ps)),
               bytes_read=sum(b['bytes'] for b in blobs), name_hit_lines=len(names_hits),
               shape_occurrences=len(candidates), header_groups=len(groups),
               requested_names=requested, network_fetch_performed=False,
               scope='ALL locally available refs, including heads/origin/deliver/deliv/delivery/fill/review/prhead namespaces and tags; TCSlib/**/*.lean only. Candidate enumeration+inspection, not semantic completeness or live GitHub PR enumeration.')
dump('summary.json', summary)
print(json.dumps(summary, indent=2))
print('\nHEADER GROUPS')
for key, group in groups.items():
    print(key, group['name'], len(group['occurrences']), group['normalized_header'][:250])
