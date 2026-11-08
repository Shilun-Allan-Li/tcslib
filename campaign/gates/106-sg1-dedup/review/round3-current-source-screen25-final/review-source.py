"""Read-only depth-aware source freeze and fresh canonical CLI lint of25 exports."""
from pathlib import Path
import collections, datetime, difflib, hashlib, json, re, subprocess, sys, time

sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final'
C=json.loads((OUT/'capture.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,x):(OUT/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
(OUT/'review-source.py').write_bytes(Path(__file__).read_bytes())
screen=(ROOT/'scripts/copy-text-screen-v3.py').read_text()
sys.argv=['parser-only',C['temporary_trees']['head'],*C['population']]
helpers={};exec(compile(screen.split('decls = []')[0],'<canonical-v3-parser-definitions-only>','exec'),helpers)

def header(t):
    text=helpers['strip'](t).strip();bd=helpers['body'](text)
    return ' '.join((text[:-len(bd)] if bd else text).split())
assert header('theorem sample (c : Cfg (input := x)) : c = c := by rfl')=='theorem sample (c : Cfg (input := x)) : c = c :='
assert header('def sample : Nat := 3')=='def sample : Nat :='
assert header('structure Example where\n  n : Nat')=='structure Example'
freeze_tool=ROOT/'devtools/seyoon/declfreeze.py';fs=freeze_tool.read_text()
assert fs.count('a = chunks(open(sys.argv[1]).read())')==1
definitions={};exec(compile(fs.split('a = chunks(open(sys.argv[1]).read())')[0],'<canonical-declfreeze-definitions-only>','exec'),definitions)
definitions['stmt']=header
freeze=[]
alltermnames={side:[] for side in ['base','head']}
for path in C['population']:
    versions={side:(OUT/'inputs'/side/(path+'.txt')).read_text() for side in ['base','head']}
    indexed={side:{name:dict(private=private,text=text,header=header(text)) for name,private,text in definitions['chunks'](src)} for side,src in versions.items()}
    a,b=indexed['base'],indexed['head'];pubA={k for k,r in a.items() if not r['private']};pubB={k for k,r in b.items() if not r['private']}
    common=a.keys()&b.keys()
    changed_headers=[dict(name=k,base=a[k]['header'],head=b[k]['header']) for k in sorted(common) if a[k]['header']!=b[k]['header']]
    visibility=[k for k in sorted(common) if a[k]['private']!=b[k]['private']]
    changed_source=[dict(name=k,private=b[k]['private'],base_sha256=sha(a[k]['text'].encode()),head_sha256=sha(b[k]['text'].encode())) for k in sorted(common) if a[k]['text']!=b[k]['text']]
    public_changed=[r['name'] for r in changed_source if not r['private']]
    imports={side:re.findall(r'^import\s+(\S+)',text,re.M) for side,text in versions.items()}
    attrs={side:[s for s in text.splitlines() if re.match(r'^\s*(?:@\[|attribute\b)',s)] for side,text in versions.items()}
    termchanges=[]
    for side,items in indexed.items():
        for name,row in items.items():
            kind=re.search(r'\b(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b',row['header']).group(1)
            if kind not in ['theorem','lemma']:
                alltermnames[side].append((path,name))
                if side=='head' and name in a and helpers['strip'](a[name]['text']).split()!=helpers['strip'](row['text']).split():termchanges.append(name)
    assert not(pubB-pubA or pubA-pubB or changed_headers or visibility or termchanges),path
    assert attrs['base']==attrs['head'],path
    freeze.append(dict(path=path,counts={side:dict(public=sum(not r['private'] for r in rows.values()),private=sum(r['private'] for r in rows.values())) for side,rows in indexed.items()},
        public_added=sorted(pubB-pubA),public_removed=sorted(pubA-pubB),changed_common_headers=changed_headers,visibility_changes=visibility,
        private_added=sorted(k for k in b.keys()-a.keys() if b[k]['private']),private_removed=sorted(k for k in a.keys()-b.keys() if a[k]['private']),
        changed_source_chunks=changed_source,public_changed_chunks=public_changed,imports=imports if imports['base']!=imports['head'] else None,
        attributes_identical=True,term_changes=termchanges))
assert sorted(alltermnames['base'])==sorted(alltermnames['head'])
added=[n.split('.')[-1] for r in freeze for n in r['private_added']];removed=[n.split('.')[-1] for r in freeze for n in r['private_removed']]
assert sorted(added)==sorted(['counterSpan_iff_segment','dgSpan_iff_segment','tautDualSegment_iff_segment'])
assert sorted(removed)==sorted(['counter_span_append','dgSpan_add','tautDual_segment_add'])
save('source-freeze.json',dict(method='Canonical declfreeze chunks/namespace/anonymous-instance parser with depth-aware v3 header delimiter replacing only its naive first-:= statement splitter; comments/whitespace ignored for statement comparison. Raw sources/diffs retain all text.',nested_input_header_control_passed=True,
    all25_public_names_headers_visibility_preserved=True,all_common_private_headers_preserved=True,
    all_source_term_declaration_keys_identical=True,no_changed_source_term_bodies=True,
    note='Source parser excludes notation/macro-generated declarations; this is not a compiled constant census or proof/type check.',files=freeze))

lint_tools={'scripts/style_lint.py':'e7f8da764a22bd61c3b2cecca7920436f20bf172d24c81648cfee81a5862c144',
            'scripts/campaign_style_lint.py':'65c420ea2f33165c674c13bf181995543133cd4b63290631655e31a4b3b29e2e'}
provenance=[]
for tool,digest in lint_tools.items():
    data=(ROOT/tool).read_bytes();assert sha(data)==digest
    assert data==git('show',C['base']+':'+tool)==git('show',C['head']+':'+tool)
    (OUT/'tools'/(Path(tool).name+'.txt')).write_bytes(data)
    for side in ['base','head']:
        target=Path(C['temporary_trees'][side])/tool;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    provenance.append(dict(tool=tool,sha256=digest,actual_equals_BASE_HEAD=True))
save('lint-tool-provenance.json',provenance)
results={}
for side in ['base','head']:
    tree=Path(C['temporary_trees'][side]);results[side]={}
    for tool in ['style','campaign']:
        command=['python3','-I',str(tree/'scripts'/('style_lint.py' if tool=='style' else 'campaign_style_lint.py'))]
        command+=list(C['population']) if tool=='style' else ['TCSlib','--check8b']
        start=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.time()
        r=subprocess.run(command,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        (OUT/(tool+'-'+side+'.out')).write_bytes(r.stdout);(OUT/(tool+'-'+side+'.stderr.out')).write_bytes(r.stderr)
        if tool=='style':
            findings=[s for s in r.stdout.decode().splitlines() if s.strip()]
            counts={'findings':len(findings)}
            assert re.search(r'\b'+str(len(findings))+r' findings in 25 files\b',r.stderr.decode())
        else:
            findings=[s for s in r.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',s)]
            counts={k:sum(s.startswith(k) for s in findings) for k in ['FAIL','WARN','INFO']}
            assert 'over 25 files' in r.stdout.decode()
        row=dict(command=command,cwd=str(tree),start_utc=start,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.time()-tick,exit=r.returncode,
            stdout_sha256=sha(r.stdout),stderr_sha256=sha(r.stderr),counts=counts,findings=findings)
        save(tool+'-'+side+'-run.json',row);results[side][tool]=row
normalize=lambda s:re.sub(r'\bline \d+\b','line <LINE>',re.sub(r'\b\d+ lines\b','<LINES> lines',re.sub(r':\d+:',':LINE:',s)))
delta={}
for tool in ['style','campaign']:
    aa={normalize(s) for s in results['base'][tool]['findings']};bb={normalize(s) for s in results['head'][tool]['findings']}
    delta[tool]=dict(normalized_new=sorted(bb-aa),normalized_gone=sorted(aa-bb))
save('lint-results.json',dict(method='Fresh unmodified canonical CLI subprocesses on the same full25 exact source exports; campaign --check8b. Only copy-text BASE is adopted; these lints are freshly run.',sides=results,delta=delta,scope='Lint of the named archive population, not global facade/import-closure validation. Inherited failures/warnings are reported, not waived.'))
save('rule-snapshots.json',[dict(path=p,sha256=sha((ROOT/p).read_bytes())) for p in ['policy.md','workflow.md','campaign/maintainer/WORKFLOW.md','campaign/standards/TEMPLATE.md','campaign/duplication-ledger.md']])
(OUT/'rule-context.txt').write_text('\n'.join((ROOT/'campaign/duplication-ledger.md').read_text().splitlines()[662:752])+'\n')
print(json.dumps(dict(freeze='All public/common private headers preserved; three private helper replacements only; no term/attribute changes.',
    lints={side:{tool:row['counts'] for tool,row in values.items()} for side,values in results.items()},delta=delta),indent=2))
