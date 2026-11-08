"""Adopt verified actual BASE CLIs; execute fresh HEAD CLIs and term/attribute freeze."""
from pathlib import Path
import ast, datetime, hashlib, json, re, subprocess, sys, time
sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final79'
OLD=OUT.parent/'round3-current-source-screen25-final'
C=json.loads((OUT/'capture.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,x):(OUT/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
(OUT/'review-lints-data.py').write_bytes(Path(__file__).read_bytes())
assert sha((OLD/'SHA256SUMS').read_bytes())=='43b179e6b7abc5cca8cbca07c93e05f8a5d543d24627f521c2d20a3b1cd4f4ec'
for line in (OLD/'SHA256SUMS').read_text().splitlines():
    digest,path=line.split('  ',1);assert sha((OLD/path).read_bytes())==digest
tools={'style':('scripts/style_lint.py','e7f8da764a22bd61c3b2cecca7920436f20bf172d24c81648cfee81a5862c144'),
       'campaign':('scripts/campaign_style_lint.py','65c420ea2f33165c674c13bf181995543133cd4b63290631655e31a4b3b29e2e')}
results={'base':{},'head':{}}
for label,(tool,digest) in tools.items():
    data=(ROOT/tool).read_bytes();assert sha(data)==digest
    for commit in [C['base'],C['head']]:assert subprocess.run(['git','-C',str(ROOT),'show',commit+':'+tool],check=True,stdout=subprocess.PIPE).stdout==data
    (OUT/'tools'/(Path(tool).name+'.txt')).write_bytes(data)
    assert (OLD/'tools'/(Path(tool).name+'.txt')).read_bytes()==data
    for name in [label+'-base.out',label+'-base.stderr.out',label+'-base-run.json']:(OUT/name).write_bytes((OLD/name).read_bytes())
    base=json.loads((OUT/(label+'-base-run.json')).read_text())
    assert base['stdout_sha256']==sha((OUT/(label+'-base.out')).read_bytes()) and base['stderr_sha256']==sha((OUT/(label+'-base.stderr.out')).read_bytes())
    results['base'][label]=base
    tree=Path(C['temporary_trees']['head']);target=tree/tool;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    command=['python3','-I',str(target)]+(list(C['population']) if label=='style' else ['TCSlib','--check8b'])
    start=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.time();q=subprocess.run(command,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    (OUT/(label+'-head.out')).write_bytes(q.stdout);(OUT/(label+'-head.stderr.out')).write_bytes(q.stderr)
    if label=='style':
        findings=[s for s in q.stdout.decode().splitlines() if s.strip()];counts={'findings':len(findings)}
        assert str(len(findings))+' findings in 25 files' in q.stderr.decode()
    else:
        findings=[s for s in q.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',s)]
        counts={k:sum(s.startswith(k) for s in findings) for k in ['FAIL','WARN','INFO']};assert 'over 25 files' in q.stdout.decode()
    row=dict(command=command,cwd=str(tree),start_utc=start,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.time()-tick,exit=q.returncode,
             stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr),counts=counts,findings=findings)
    save(label+'-head-run.json',row);results['head'][label]=row
norm=lambda s:re.sub(r'\bline \d+\b','line <LINE>',re.sub(r'\b\d+ lines\b','<LINES> lines',re.sub(r':\d+:',':LINE:',s)))
delta={}
for label in tools:
    a={norm(s) for s in results['base'][label]['findings']};b={norm(s) for s in results['head'][label]['findings']}
    delta[label]=dict(normalized_new=sorted(b-a),normalized_gone=sorted(a-b))
save('lint-results.json',dict(method='Actual prior25 BASE CLI outputs adopted after full source/tool/population equivalence; fresh unmodified canonical25 HEAD CLI subprocesses. No copied HEAD result and no repeated BASE lint.',sides=results,delta=delta))
save('lint-base-adoption.json',dict(source_generation=str(OLD.relative_to(ROOT)),old_manifest_sha256=sha((OLD/'SHA256SUMS').read_bytes()),source_blobs_and_population_equal=True,tool_hashes={k:v[1] for k,v in tools.items()},base_lint_rerun=False))

text=(ROOT/'scripts/copy-text-screen-v3.py').read_text();sys.argv=['parser-only',C['temporary_trees']['head'],*C['population']]
h={};exec(compile(text.split('decls = []')[0],'<v3-parser-helpers>','exec'),h)
module=ast.parse((OUT/'review-complete-headers.py').read_text());node=next(n for n in module.body if isinstance(n,ast.FunctionDef) and n.name=='header')
globals_={'h':h,'re':re};exec(compile(ast.Module(body=[node],type_ignores=[]),'<reviewed-header-function-only>','exec'),globals_);header=globals_['header']
text=(ROOT/'devtools/seyoon/declfreeze.py').read_text();ns={};exec(compile(text.split('a = chunks(open(sys.argv[1]).read())')[0],'<declfreeze-helpers>','exec'),ns);ns['stmt']=header
rows=[]
for path in C['population']:
    sources={side:(OUT/'inputs'/side/(path+'.txt')).read_text() for side in ['base','head']}
    chunks={side:{name:text for name,private,text in ns['chunks'](src)} for side,src in sources.items()}
    terms={}
    for side,items in chunks.items():
        terms[side]={}
        for name,src in items.items():
            kind=re.search(r'\b(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b',header(src)).group(1)
            if kind not in ['theorem','lemma']:terms[side][name]=' '.join(h['strip'](src).split())
    assert terms['base']==terms['head'],path
    attrs={side:[s for s in src.splitlines() if re.match(r'^\s*(?:@\[|attribute\b)',s)] for side,src in sources.items()}
    assert attrs['base']==attrs['head'],path
    rows.append(dict(path=path,source_term_count=len(terms['head']),term_names_bodies_identical=True,attributes_identical=True))
save('source-term-attribute-freeze.json',dict(method='Reviewed complete-header parser plus canonical declaration chunks; full comment/whitespace-normalized source term chunks and attribute lines compared. Not compiler-generated/notation census or Lean proof check.',all25_source_terms_attributes_identical=True,files=rows))
print(json.dumps(dict(lints={side:{label:row['counts'] for label,row in rs.items()} for side,rs in results.items()},delta=delta,source_terms_attributes='PASS'),indent=2))
