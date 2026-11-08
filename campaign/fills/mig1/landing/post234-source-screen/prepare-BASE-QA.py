from pathlib import Path
import ast,collections,datetime,hashlib,json,re,subprocess,sys,time
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
C=json.loads((OUT/'capture.json').read_text());SC=json.loads((OUT/'base-capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*a):return subprocess.run(['git','-C',str(ROOT),*a],check=True,stdout=subprocess.PIPE).stdout
assert len(C['population'])==25 and SC['population']==C['population']
code=(ROOT/'devtools/seyoon/declfreeze.py').read_text();(OUT/'tools/declfreeze.py.txt').write_text(code);ns={};exec(compile(code.split('a = chunks(open(sys.argv[1]).read())')[0],'<trusted-chunks>','exec'),ns)
current={};progress=[]
for row in SC['files']:
 path=row['path'];b=git('show',SC['commit']+':'+path);assert sha(b)==row['sha256']==sha((OUT/'inputs/base'/(path+'.txt')).read_bytes())==sha((Path(SC['tree'])/path).read_bytes())
 old=git('show',C['previous_base']+':'+path)
 cur=list(ns['chunks'](b.decode()));before=list(ns['chunks'](old.decode()));a={n:(p,t) for n,p,t in before};z={n:(p,t) for n,p,t in cur};assert len(a)==len(before) and len(z)==len(cur)
 current[path]=[dict(name=n,private=p,source_chunk_bytes=len(t.encode()),source_chunk_sha256=sha(t.encode())) for n,p,t in cur]
 progress.append(dict(path=path,current_source_sha256=sha(b),previous_source_sha256=sha(old),source_bytes_changed=b!=old,current_declarations=len(z),current_public=sum(not p for p,t in z.values()),current_private=sum(p for p,t in z.values()),previous_declarations=len(a),public_added=sorted(n for n,p,t in cur if not p and n not in a),public_removed=sorted(n for n,p,t in before if not p and n not in z),private_added=sorted(n for n,p,t in cur if p and n not in a),private_removed=sorted(n for n,p,t in before if p and n not in z)))
changed=[r['path'] for r in progress if r['source_bytes_changed']];expected=COV=json.loads((OUT/'population-coverage.json').read_text())['all_5_upstream_homes'];assert set(changed)==set(expected)
save('BASE-source-inventory.json',dict(pin=C['base'],full_files=25,inventory=current,method='Trusted namespace-aware source chunk inventory, including all sizes/privacy. Source declarations are not a compiled census. No HEAD source freeze or header approval is claimed.'))
save('BASE-upstream-source-progression.json',dict(previous_BASE=C['previous_base'],current_BASE=C['base'],changed_paths=changed,all5_expected_upstream_homes=True,files=progress,scope='Actual full current BASE vs historical API1160 source; no earlier screen adoption.'))
(OUT/'BASE-previous-to-current.diff').write_bytes(git('diff',C['previous_base'],C['base'],'--',*C['population']))
# Exact unmodified v3 parser prefix only; never executes its tiling loop.
tool=ROOT/'scripts/copy-text-screen-v3.py';source=tool.read_text();assert sha(source.encode())==SC['tool_sha256'];marker='pairs = []; total = 0';assert source.count(marker)==1
sys.argv=[str(tool),SC['tree'],*C['population']];v={};exec(compile(source.split(marker)[0],str(tool)+':parser-only','exec'),v)
index=[dict(label=v['label'](p)+'::'+name,path=p,offset=o,name=name,kind=k,normalized_body=body,body_chars=len(body)) for ((p,o),name,k,body,grams) in v['decls']];save('base-index.json',index)
results={}
for label,path in [('style','scripts/style_lint.py'),('campaign','scripts/campaign_style_lint.py')]:
 data=(ROOT/path).read_bytes();assert git('show',C['base']+':'+path)==data;(OUT/'tools'/(Path(path).name+'.txt')).write_bytes(data)
 tree=Path(SC['tree']);local=tree/path;local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(data);cmd=['python3','-I',str(local)]+(C['population'] if label=='style' else ['TCSlib','--check8b'])
 tick=time.time();start=now();q=subprocess.run(cmd,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(OUT/(label+'-base.out')).write_bytes(q.stdout);(OUT/(label+'-base.stderr.out')).write_bytes(q.stderr)
 findings=[x for x in q.stdout.decode().splitlines() if x.strip()] if label=='style' else [x for x in q.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',x)];counts=dict(findings=len(findings)) if label=='style' else {k:sum(x.startswith(k) for x in findings) for k in ['FAIL','WARN','INFO']}
 if label=='style':assert f'{len(findings)} findings in 25 files' in q.stderr.decode()
 else:assert 'over 25 files' in q.stdout.decode()
 r=dict(command=cmd,cwd=str(tree),start_utc=start,end_utc=now(),seconds=time.time()-tick,exit=q.returncode,stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr),findings=findings,counts=counts);save(label+'-base-run.json',r);results[label]=r
save('BASE-lint-results.json',dict(fresh_actual_full25_CLIs=True,pin=C['base'],sides=dict(base=results),HEAD_NOT_RUN=True))
print(json.dumps(dict(BASE_source_files_verified=25,upstream_changed_paths=changed,BASE_eligible_index=len(index),BASE_source_public=sum(r['current_public'] for r in progress),BASE_source_private=sum(r['current_private'] for r in progress),fresh_lints={k:r['counts'] for k,r in results.items()},HEAD='NOT RUN; final pushed pin required'),indent=2))
