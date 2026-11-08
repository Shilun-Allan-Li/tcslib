"""Independent data-only SG1 packet QA. Never imports or executes supplied code."""
from pathlib import Path
import ast
import base64
import collections
import datetime
import gzip
import hashlib
import io
import json
import os
import re
import subprocess
import tarfile

R = Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
G = R / 'campaign/gates/106-sg1-dedup'
P = G / 'review/round3-final-packet'
C = G / 'review/round3-final-compiled'
Q = G / 'review/round3-current-source-screen25-final79'
OUT = Path('/private/tmp/sg1-final-packet-peer-review-output')
S = Path(os.environ['TCSLIB_SCRATCH']) / 'wt-sg1'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(b):
    return hashlib.sha256(b).hexdigest()

def readj(p):
    return json.loads(p.read_text())

def git(*args):
    return subprocess.run(['git', '-C', str(S), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout

def pinned(f, row):
    data = f.read_bytes()
    assert len(data) == row['bytes'] and digest(data) == row['sha256'], str(f)
    return data

report = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'result': 'PASS bounded independent packet QA; publication remains root-owned',
          'candidate_manifest_sha256': digest((P/'MANIFEST.json').read_bytes()),
          'execution_limits': 'Own standard-library checker only. No delivered code execution, Lean, screen, snapshot/cache access, Git mutation, commit, push, dispatch, or source/canonical/frozen write.'}
assert report['candidate_manifest_sha256'] == '3bf0f54a07d9a4c96abc3a92fdbd007c593ab6788611e23fe26cd0cc438d5fed'
manifest = readj(P/'MANIFEST.json')
for row in manifest['files']:
    pinned(P/row['path'], row)
original = readj(P/'original-inputs.json')
contextual_mutable = {
    'campaign/gates/106-sg1-dedup/STATUS.md',
    'campaign/gates/106-sg1-dedup/pack-r3.md',
    'campaign/gates/106-sg1-dedup/resolutions-r2.md',
    'campaign/maintainer/HANDOFF.md',
    'campaign/duplication-ledger.md',
}
contextual_drift = []
for row in original['files']:
    b=(R/row['path']).read_bytes()
    if (len(b),digest(b)) != (row['bytes'],row['sha256']):
        assert row['path'] in contextual_mutable, row['path']
        contextual_drift.append(dict(path=row['path'],frozen_bytes=row['bytes'],frozen_sha256=row['sha256'],current_bytes=len(b),current_sha256=digest(b)))
sections = (P/'BUNDLE-FILES-candidate.txt').read_text().splitlines()
assert len(sections) == len(set(sections)) == 1539
payload_bytes = 0
frozen_payload_bytes = 0
original_by_path = {x['path']:x for x in original['files']}
for path in sections:
    b = (R/path).read_bytes()
    b.decode('utf-8')
    payload_bytes += len(b)
    frozen_payload_bytes += original_by_path[path]['bytes'] if path in original_by_path else len(b)
assert frozen_payload_bytes == 98855551
assert payload_bytes-frozen_payload_bytes == sum(x['current_bytes']-x['frozen_bytes'] for x in contextual_drift if x['path'] in sections)
enc = readj(P/'encoding-receipt.json')
aliases = {}
for row in enc['transforms']:
    o = row['original']; b = (R/row['encoding_path']).read_bytes()
    zipped = base64.b64decode(b''.join(b.split()), validate=True)
    raw = gzip.decompress(zipped)
    assert (len(b), digest(b)) == (row['encoded_utf8_bytes'], row['encoded_utf8_sha256'])
    assert (len(zipped), digest(zipped)) == (row['gzip_bytes'], row['gzip_sha256'])
    assert raw == pinned(R/o['path'], o)
    buf = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', compresslevel=9, mtime=0, fileobj=buf) as stream:
        stream.write(raw)
    assert buf.getvalue() == zipped
    aliases[o['path']] = row['encoding_path']
assert len(aliases) == 40 and len(set(aliases.values())) == 31
binary = {}
for row in enc['binary_gzip_equivalents']:
    b = pinned(R/row['path'], row)
    assert b == base64.b64decode((R/row['represented_by']).read_bytes())
    binary[row['path']] = row['represented_by']
original_paths = {row['path'] for row in original['files']}
representations = (original_paths-set(aliases)) | set(aliases.values())
assert representations <= set(sections)
selection = readj(P/'input-selection.json')
assert set(selection['plain_sections']) == original_paths-set(aliases)
assert set(selection['encoded_sections']) == set(aliases.values())
supplemental = readj(P/'supplemental-inputs.json')['files']
for row in supplemental:
    pinned(R/row['path'], row)
    assert row['path'] in sections
represented = set(sections) | set(aliases) | set(binary)
gate_files = [f for f in G.rglob('*') if f.is_file() and not f.is_relative_to(P)
              and 'round3-final-packet-peer-review' not in str(f)]
omitted = [str(f.relative_to(R)) for f in gate_files if str(f.relative_to(R)) not in represented]
assert omitted == ['campaign/gates/106-sg1-dedup/pack-r3.md'], omitted
canonical_pack_still_unissued = (G/'pack-r3.md').read_bytes() == (P/'unissued-pack-r3-before.md').read_bytes()
report['inventory'] = dict(candidate_manifest_payloads=len(manifest['files']),
    original_inputs=len(original['files']), original_input_bytes=sum(x['bytes'] for x in original['files']),
    initial_original_input_drift=[], current_publication_context_drift=contextual_drift, sections=len(sections), all_sections_UTF8=True, frozen_payload_bytes=frozen_payload_bytes, live_payload_bytes_at_check=payload_bytes,
    original_aliases=len(aliases), distinct_encoded_sections=len(set(aliases.values())), binary_equivalents=len(binary),
    original_representations_omitted=[], additional_candidate_and_supplemental_sections=len(set(sections)-representations),
    entire_gate106_files_except_candidate=len(gate_files),
    coverage_exception='Unissued canonical pack-r3.md was exactly preserved by unissued-pack-r3-before.md at initial check; candidate pack replaces its role.',
    canonical_pack_still_unissued=canonical_pack_still_unissued)

freeze_checks = []
for folder in ['round3-current-source-screen25-final79','round3-current-source-screen25-final','round3-current-source-screen25']:
    d = G/'review'/folder
    lines = (d/'SHA256SUMS').read_text().splitlines()
    for line in lines:
        h, path = line.split('  ', 1)
        assert digest((d/path).read_bytes()) == h
    allfiles = [str(x.relative_to(R)) for x in d.rglob('*') if x.is_file()]
    assert set(allfiles) <= represented
    freeze_checks.append(dict(folder=str(d.relative_to(R)), manifest_sha256=digest((d/'SHA256SUMS').read_bytes()),
                             manifest_payloads=len(lines), full_folder_files=len(allfiles)))
for row in readj(C/'MANIFEST.json')['files']:
    pinned(C/row['path'], row)
freeze_checks.append(dict(folder=str(C.relative_to(R)), manifest_sha256=digest((C/'MANIFEST.json').read_bytes()),
                         manifest_payloads=len(readj(C/'MANIFEST.json')['files']), full_folder_files=sum(f.is_file() for f in C.rglob('*'))))
report['frozen_evidence'] = freeze_checks

head = git('rev-parse', 'HEAD').decode().strip()
base = git('rev-parse', '3023dc1408c3d216fc07a7cbba9ae30135b861ed^{commit}').decode().strip()
git('cat-file','-e',head+'^{commit}'); git('cat-file','-e',base+'^{commit}')
assert head == manifest['source_head'] and not git('status','--porcelain=v1')
git('merge-base','--is-ancestor',base,head)
capture = readj(Q/'capture.json')
assert capture['head'] == head and capture['base'] == base and len(capture['population']) == 25
source_checks = []
sources = {}
for side in ['base', 'head']:
    archive = base64.b64decode((Q/(side+'.tar.base64.txt')).read_bytes())
    assert digest(archive) == capture['sides'][side]['archive_sha256']
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        assert {m.name for m in tar.getmembers() if m.isfile()} == set(capture['population'])
        for row in capture['sides'][side]['files']:
            path = row['path']; cap_path = Q/'inputs'/side/(path+'.txt')
            b = pinned(cap_path, row)
            assert b == tar.extractfile(path).read() == git('show', capture[side]+':'+path)
            assert git('rev-parse', capture[side]+':'+path).decode().strip() == row['blob']
            assert str(cap_path.relative_to(R)) in selection['plain_sections'] and str(cap_path.relative_to(R)) in sections
            sources[side, path] = b
            source_checks.append(dict(side=side, path=path, bytes=len(b), sha256=digest(b), git_blob=row['blob']))
changed = git('diff','--name-only',base+'...'+head,'--','*.lean').decode().splitlines()
assert set(changed) == set(capture['changed_files']) and len(changed) == 5
no_api = subprocess.run(['git','-C',str(S),'grep','-n','exists_first_entry_of_fixed',head,'--','TCSlib'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert no_api.returncode == 1 and not no_api.stdout
hard = sources['head','TCSlib/Complexity/CookLevin/Hardness.lean'].decode()
taut = sources['head','TCSlib/Complexity/ClassNP/Tautology.lean'].decode()
assert 'exact FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU' in taut
added_imports = re.findall(r'^\+import (.+)$',git('diff',base,head,'--','TCSlib/Complexity/CookLevin/Hardness.lean').decode(),re.M)
assert len(added_imports)==2 and set(added_imports) == {'TCSlib.Complexity.ClassNP.PolyTimePrefix','TCSlib.Complexity.ClassNP.PolyTimeBlockLoop'}
assert 'length_pair_components_le' in hard
report['source'] = dict(worktree=str(S), head=head, base=base, source_clean=True, base_is_ancestor=True,
    changed_Lean_files=changed, all50_current_captures_equal_git_and_archive=True,
    all50_captures_plaintext=True, added_Hardness_imports=added_imports,
    first_live_API_absent_from_SG1=True, raw_Tautology_direct_repoint_present=True,
    complete50_input_pins=source_checks)

screen = {}
for side in ['base','head']:
    index_list=readj(Q/(side+'-index.json')); index={x['label']:x for x in index_list}
    assert len(index) == len(index_list)
    assert all(len(x['normalized_body']) == x['body_chars'] for x in index_list)
    lines=(Q/(side+'.out')).read_text().splitlines()
    summary=re.fullmatch(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',lines[0])
    assert summary
    rows=[]
    for line in lines[1:]:
        m=re.fullmatch(r'\s+(.+?)  reproduces  (.+?): (\d+)/(\d+) = (\d+)%',line); assert m
        a,b,n,d,p=m.groups(); assert index[a]['kind']==index[b]['kind'] and int(d)==index[b]['body_chars']
        rows.append(dict(a=a,b=b,shared=int(n),denominator=int(d),printed_percent=int(p),kind=index[a]['kind'],cross_file=index[a]['path']!=index[b]['path']))
    assert rows == readj(Q/(side+'-candidates.json'))
    assert (len(index),len(rows),sum(x['shared'] for x in rows)) == (int(summary[1]),int(summary[2]),int(summary[3].replace(',','')))
    assert len({(x['a'],x['b']) for x in rows}) == len(rows)
    run=readj(Q/(side+'-run.json')); assert run['exit']==0 and run['output_sha256']==digest((Q/(side+'.out')).read_bytes())
    screen[side]=dict(index=index, rows=rows)
a={(x['a'],x['b']):x for x in screen['base']['rows']};b={(x['a'],x['b']):x for x in screen['head']['rows']}
new={k:b[k] for k in b.keys()-a.keys()};gone={k:a[k] for k in a.keys()-b.keys()};changes={k:dict(base=a[k],head=b[k]) for k in a.keys()&b.keys() if a[k]!=b[k]}
assert (len(new),len(gone),len(changes)) == (2,20,13)
classes=readj(Q/'head-delta-classification.json')['rows'];assert len(classes)==35
for c in classes:
    row=c['row']; keyrow=row['head'] if c['change']=='changed' else row; key=(keyrow['a'],keyrow['b'])
    assert {'new':new,'gone':gone,'changed':changes}[c['change']][key] == row
assert len({(c['change'],(c['row']['head'] if c['change']=='changed' else c['row'])['a'],(c['row']['head'] if c['change']=='changed' else c['row'])['b']) for c in classes})==35
terms={side:{k:r['normalized_body'] for k,r in screen[side]['index'].items() if r['kind']=='term'} for side in screen}
assert terms['base']==terms['head'] and len(terms['base'])==435
termrows=[[x for x in screen[side]['rows'] if x['kind']=='term'] for side in ['base','head']]
assert termrows[0]==termrows[1] and len(termrows[0])==259
old={(x['a'],x['b']):x for x in readj(G/'review/round3-current-source-screen25-final/head-candidates.json')}
assert not(b.keys()-old.keys()) and len(old.keys()-b.keys())==4
assert all(old[k]==b[k] for k in b) and all(old[k]['a']=='Tautology.lean::taut_comp_on_image' for k in old.keys()-b.keys())
report['screen']={side:dict(declarations=len(screen[side]['index']),candidates=len(screen[side]['rows']),reproduced_chars=sum(x['shared'] for x in screen[side]['rows'])) for side in screen}
report['screen'].update(new=2,gone=20,changed=13,all35_dispositions_exact=True,identical_term_spans=435,identical_term_candidates=259,previous63_only_four_Tautology_directed_rows_gone=True,BASE_adopted_not_reexecuted=True)

compiled={}
for label in ['Base','Head']:
    m=readj(C/('map-'+label+'.json')); rows=m['census']; raw={}
    for stage in ['census-v1','types-v1','ciattrs-v1']:
        receipt=readj(C/(label+'-'+stage+'-run.json')); encoded=(C/(label+'-'+stage+'.out.gz.b64')).read_bytes()
        packed=base64.b64decode(encoded);data=gzip.decompress(packed)
        assert receipt['exit']==receipt['errors']==receipt['warnings']==0
        assert (len(encoded),digest(encoded))==(receipt['base64_bytes'],receipt['base64_sha256'])
        assert (len(packed),digest(packed))==(receipt['gzip_bytes'],receipt['gzip_sha256'])
        assert (len(data),digest(data))==(receipt['raw_utf8_bytes'],receipt['raw_utf8_sha256'])
        assert digest((C/('Metadata-'+stage+'.lean.txt')).read_bytes())==receipt['input_sha256']
        raw[stage]=data.decode()
    constant_matches=list(re.finditer(r'^CONSTANT (\S+) module=(\S+) kind=(\S+) private=(true|false) internal=(true|false)$',raw['census-v1'],re.M))
    assert len(constant_matches)==len(rows)
    constants={x[1]:dict(owner=x[2],kind=x[3],private=x[4]=='true',internal=x[5]=='true') for x in constant_matches}
    ax={x[1]:[v.strip() for v in x[2].split(',') if v.strip()] for x in re.finditer(r'^ALLAX\|([^|\n]+)\|\[([^\]]*)\]',raw['census-v1'],re.M)}
    pax={x[1]:[v.strip() for v in x[2].split(',') if v.strip()] for x in re.finditer(r'^PUBLICAX\|([^|\n]+)\|\[([^\]]*)\]',raw['census-v1'],re.M)}
    assert set(constants)==set(rows)==set(ax) and set(pax)=={n for n in rows if not rows[n]['private']}
    for n in rows:
        assert all(rows[n][k]==v for k,v in constants[n].items()) and rows[n]['axioms']==ax[n]
        if n in pax: assert pax[n]==ax[n]
    types=raw['types-v1']; markers=list(re.finditer(r'^(?:TYPE_REPR\|([^|\n]+)\||TYPECOMPLETE\|constants=(\d+))',types,re.M))
    assert markers[-1][2]==str(len(rows)) and len(markers)==len(rows)+1
    for i,x in enumerate(markers[:-1]):
        value=types[x.end():markers[i+1].start()].removesuffix('\n').encode(); row=rows[x[1]]['type_repr']
        assert (len(value),digest(value),i)==(row['utf8_bytes'],row['sha256'],row['block'])
    attrs={};ci={};simp=collections.defaultdict(list)
    for line in raw['ciattrs-v1'].splitlines():
        if line.startswith(('CI|','ATTR|','SIMP_RULE|')):
            tag,n,value=line.split('|',2); value=json.loads(value)
            if tag=='SIMP_RULE':simp[n].append(value)
            else:(ci if tag=='CI' else attrs)[n]=value
    assert set(ci)==set(attrs)==set(rows)
    assert dict(simp)==m['simp_rules']
    for n in rows:assert rows[n]['ci']==ci[n] and rows[n]['attributes']==attrs[n]
    compiled[label]=m
left,right=compiled['Base']['census'],compiled['Head']['census'];shared=left.keys()&right.keys();added=right.keys()-left.keys();removed=left.keys()-right.keys()
assert (len(left),len(right),len(added),len(removed))==(7101,7063,6,44)
publicA={n for n,r in left.items() if not r['private']};publicB={n for n,r in right.items() if not r['private']}
assert publicA==publicB and len(publicA)==1351
fields=['owner','kind','private','internal','ci','attributes','axioms']
for n in publicA:assert all(left[n][k]==right[n][k] for k in fields) and left[n]['type_repr']['sha256']==right[n]['type_repr']['sha256']
assert all(right[n]['private'] for n in added) and all(left[n]['private'] for n in removed)
assert compiled['Base']['simp_rules']==compiled['Head']['simp_rules'] and sum(len(x) for x in compiled['Head']['simp_rules'].values())==168
nonstandard={side:{n:r for n,r in rows.items() if set(r['axioms'])-STANDARD} for side,rows in [('Base',left),('Head',right)]}
assert nonstandard['Base'].keys()==nonstandard['Head'].keys() and len(nonstandard['Head'])==9
for n in nonstandard['Head']:assert left[n]['axioms']==right[n]['axioms'] and right[n]['owner']=='TCSlib.Complexity.TuringMachine.Build.Primitives'
assert all(set(right[n]['axioms'])<=STANDARD for n in added)
assert all(not((set(right[n]['axioms'])-set(left[n]['axioms']))-STANDARD) for n in shared)
typechanges=sorted(n for n in shared if left[n]['type_repr']['sha256']!=right[n]['type_repr']['sha256']);axchanges=sorted(n for n in shared if set(left[n]['axioms'])!=set(right[n]['axioms']))
assert len(typechanges)==10 and len(axchanges)==1 and axchanges[0].endswith('.clA5Pair_sizes')
roots=readj(C/'all-current-repaired-roots.json');selected=set();descendants=set()
for row in roots['roots']:
    n=row['name']; assert n in right and row['axioms']==right[n]['axioms']
    ds={x for x in right if x.startswith(n+'.')}
    actual={x['name'] if isinstance(x,dict) else x for x in row['descendants']}
    assert ds==actual
    selected.add(n);selected.update(ds);descendants.update(ds)
assert (len(roots['roots']),len(descendants),len(selected))==(43,93,136)
assert all(set(right[n]['axioms'])<=STANDARD for n in selected)
inventory=readj(C/'source-authored-inventory.json')['owners']
for side in ['base','head']:
    assert sum(x[side+'_declarations'] for x in inventory)==1986 and sum(x[side+'_public'] for x in inventory)==349
report['compiled']=dict(raw_six_stages_independently_reparsed=True,base_constants=len(left),head_constants=len(right),
    base_private=sum(x['private'] for x in left.values()),head_private=sum(x['private'] for x in right.values()),
    exact_nonprivate=len(publicA),effective_owned_simp_rules=168,private_added=len(added),private_removed=len(removed),
    common_private_type_changes=len(typechanges),common_AXIOM_changes=axchanges,retained_Primitives_nonstandard_names=sorted(nonstandard['Head']),
    current_standard_roots=43,current_standard_descendants=93,distinct_standard_selected=136,source_declarations_per_side=1986,
    source_public_per_side=349,source_private_per_side=1637)

replays=[]
for folder,tag,expected,sorries in [('current-replay-r3','msg5',329,66),('final-replay-msg6','msg6',26,0),('final-replay-msg7','msg7',2,0)]:
    d=G/'evidence'/folder; receipt=readj(d/'receipt.json'); text=(d/('replay-'+tag+'.log')).read_text()
    lines=re.findall(r'^(TCSlib/\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',text,re.M)
    order=(d/('down-'+tag+'.txt')).read_text().splitlines()
    assert len(lines)==expected and [x[0] for x in lines]==order and all(x[1:3]==('0','0') for x in lines)
    assert sum(int(x[3]) for x in lines)==sorries and text.splitlines()[-1]==f'# modules={expected} failed=0'
    launches=(d/('replay-'+tag+'-launches.log')).read_text().splitlines(); assert len(launches)==expected
    for line,m in zip(launches,order): assert re.match(r'pid=\d+ -j4 '+re.escape(m)+r'\.lean -o ',line)
    assert (d/('replay-'+tag+'-static.txt')).read_text().strip()==f'modules {expected}, mismatches 0, static total {sorries}'
    for row in receipt['evidence']:pinned(d/row['path'],row)
    driver=(d/('replay-'+tag+'.sh')).read_text();assert 'cp -cR "$S/oleans-' in driver and 'nice -n 10 bash scripts/lean_check_tree.sh' in driver
    assert receipt['result']=='PASS' and receipt['pipeline_exit']==0
    replays.append(dict(generation=tag,source=receipt['head'],modules=expected,failures=0,static_mismatches=0,admissions=sorries,per_module_enforced_j4=expected,whole_clone_driver_inspected=True))
report['replay']=dict(sequence=replays,limits='Reparsed completed evidence, not reexecuted. No snapshot read or reconstruction. MSG6/7 scope admissions0 do not erase campaign admissions66; no fictional final329 run.')

# Reconstruct all three source import graphs independently, using only committed source.
# This reads Git archives into memory; no source is extracted or code imported/executed.
closure_checks=[]
previous=base
for replay in replays:
    rev=replay['source']; tag=replay['generation']
    graph={}
    with tarfile.open(fileobj=io.BytesIO(git('archive',rev,'TCSlib'))) as archive:
        for member in archive.getmembers():
            if not(member.isfile() and member.name.endswith('.lean')):continue
            text=archive.extractfile(member).read().decode();i=0;imports=[]
            while i<len(text):
                if text[i].isspace():i+=1
                elif text.startswith('--',i):
                    e=text.find('\n',i);i=len(text) if e<0 else e
                elif text.startswith('/-',i):
                    depth=1;i+=2
                    while depth and i<len(text):
                        if text.startswith('/-',i):depth+=1;i+=2
                        elif text.startswith('-/',i):depth-=1;i+=2
                        else:i+=1
                    assert depth==0
                elif text.startswith('import ',i):
                    e=text.find('\n',i);e=len(text) if e<0 else e
                    imports += [x for x in text[i+7:e].split('--')[0].split() if x.startswith('TCSlib')]
                    i=e
                else:break
            graph[member.name[:-5].replace('/','.')]=imports
    changed_since=git('diff','--name-only',previous,rev,'--','*.lean').decode().splitlines()
    targets=[x[:-5].replace('/','.') for x in changed_since]
    reverse=collections.defaultdict(set)
    for n,imports in graph.items():
        for imported in imports:reverse[imported].add(n)
    closure=set();todo=list(targets)
    while todo:
        n=todo.pop()
        if n in closure:continue
        closure.add(n);todo.extend(reverse[n])
    closure.discard('TCSlib')
    order=[];visited=set()
    def visit(n):
        if n in visited:return
        visited.add(n)
        for imported in sorted(graph[n]):
            if imported in closure:visit(imported)
        order.append(n.replace('.','/'))
    for n in sorted(closure):visit(n)
    folder={'msg5':'current-replay-r3','msg6':'final-replay-msg6','msg7':'final-replay-msg7'}[tag]
    assert order==(G/'evidence'/folder/('down-'+tag+'.txt')).read_text().splitlines()
    closure_checks.append(dict(generation=tag,previous=previous,source=rev,source_Lean_modules=len(graph),changed_files=changed_since,
                               independently_reconstructed_downstream_count=len(order),complete_order_exact=True))
    previous=rev
report['replay']['independent_full_source_import_closures']=closure_checks

accounting=readj(P/'family-accounting.json');prior=readj(G/'review/round3-host-accounting-addon/disjoint-accounting.json')
prior_set=set(accounting['prior_named_affected_set']); live_set={x['name'] for x in accounting['FE_LIVE_1_current_Hardness_members']}
assert prior_set==set(prior['new_named_affected_set']) and len(prior_set)==49
assert len(live_set)==5 and not(prior_set&live_set) and prior_set|live_set==set(accounting['named_affected_union']) and len(prior_set|live_set)==54
quotes=(P/'FE-LIVE-current-Hardness-quotes.md').read_text();blocks=dict(re.findall(r'^## (\w+)\n\n```lean\n(.*?)\n```',quotes,re.M|re.S))
base_hard=sources['base','TCSlib/Complexity/CookLevin/Hardness.lean'].decode()
for row in accounting['FE_LIVE_1_current_Hardness_members']:
    b=blocks[row['name']].encode()
    assert b.decode() in hard and b.decode() in base_hard
    assert (len(b),digest(b))==(row['source_chunk_bytes'],row['actual_source_chunk_sha256'])
live_ruling=readj(R/'campaign/gates/119-mig1-followup-api/ruling-live-stop.json')
host_ruling=readj(G/'review/unary-host-ruling-proposal/ruling.json')
assert live_ruling['family']=='FE-LIVE-1' and live_ruling['user_answer']=='Accept this scheduled debt (Recommended)'
assert host_ruling['user_answer']=='Accept scheduled host debt (Recommended)' and host_ruling['count']==14
assert 'None-halt' in live_ruling['limits'] and 'on-image class wrapper is excluded' in host_ruling['limits']
report['debt_scope']=dict(seven_SG1_kinds_and_FE_LIVE_separate=True,prior_named_affected=49,live_members=5,intersection=0,union_named_affected=54,denominator=544,
    five_current_live_proof_chunks_byte_exact_in_both_Git_captures=True,
    interpretation='Named affected union only; not54copies, full census, or one-fifth clearance. FE-LIVE excludes None-halt/future copies. clNative_image remains bounded/unacknowledged, distinct from exact raw Tautology composition repoint.')

dependency_checks=[]
required=['scripts/copy-text-screen-v3.py','devtools/seyoon/declfreeze.py','devtools/seyoon/pairdiff.py','scripts/campaign_style_lint.py','scripts/style_lint.py','devtools/seyoon/mkdownmulti.py','devtools/seyoon/graph.py','policy.md','workflow.md','campaign/standards/TEMPLATE.md','campaign/maintainer/WORKFLOW.md']
missing_dependencies=sorted(set(required)-represented)
assert missing_dependencies==['devtools/seyoon/graph.py']
for f in sorted(Q.glob('*.py')):
    tree=ast.parse(f.read_text())
    dependency_checks.append(dict(path=str(f.relative_to(R)),sha256=digest(f.read_bytes()),ast_parsed_only=True))
report['checker_dependencies']=dict(required_tools_and_standards=required,missing_from_frozen_candidate=missing_dependencies,
    fix='Add exact graph.py generation dependency with provenance to root-owned final publication supplement/list; frozen candidate remains immutable.',
    full_historical63_and_D0_folder_dependencies_present=True,statically_read_final79_checkers=dependency_checks,delivered_code_executed=False)
report['result']='PASS bounded independent frozen-data QA; one concrete dependency inclusion required in final publication'
report['publication_pending']='Root must finalize mutable canonical chronology/status, records pin, rendered bundle prologue/hash/sections, exchange commit/path and prompt. The frozen candidate does not self-pin its own future commit.'
OUT.mkdir(exist_ok=False)
(OUT/'QA.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['source','checker_dependencies']},indent=2,ensure_ascii=False))
