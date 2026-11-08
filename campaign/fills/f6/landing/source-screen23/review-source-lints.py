"""Fresh source-only F6 preservation check and unmodified full23 lint CLIs."""
from pathlib import Path
import ast, datetime, hashlib, json, re, subprocess, sys, time
sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/fills/f6/landing/source-screen23'
C=json.loads((OUT/'capture.json').read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name,x): (OUT/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
(OUT/'review-source-lints.py').write_bytes(Path(__file__).read_bytes())
text=(ROOT/'scripts/copy-text-screen-v3.py').read_text()
sys.argv=['parser-only',C['temporary_trees']['head'],*C['population']]
h={};exec(compile(text.split('decls = []')[0],'<canonical-v3-parser-helpers>','exec'),h)
# Reuse only the previously read depth/type-let delimiter function, not its SG1 task.
prior=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final79/review-complete-headers.py'
module=ast.parse(prior.read_text()); node=next(n for n in module.body if isinstance(n,ast.FunctionDef) and n.name=='header')
helper=ast.get_source_segment(prior.read_text(),node)+'\n'
(OUT/'tools/complete-header-function.py.txt').write_text(helper)
globals_={'h':h,'re':re};exec(compile(ast.Module(body=[node],type_ignores=[]),'<reviewed-complete-header-function>','exec'),globals_);header=globals_['header']
controls=[
 ('theorem t (c : Cfg (input := x)) : c = c := by rfl','theorem t (c : Cfg (input := x)) : c = c :='),
 ('theorem t : let arg := [true]; arg = arg := by rfl','theorem t : let arg := [true]; arg = arg :='),
 ('theorem t : let a := let b := 0; b; a = a := by rfl','theorem t : let a := let b := 0; b; a = a :='),
 ('structure Example where\n n : Nat','structure Example')]
for source,expected in controls: assert header(source)==expected
freeze=(ROOT/'devtools/seyoon/declfreeze.py').read_text();(OUT/'tools/declfreeze.py.txt').write_text(freeze)
ns={};exec(compile(freeze.split('a = chunks(open(sys.argv[1]).read())')[0],'<canonical-declfreeze-helpers>','exec'),ns);ns['stmt']=header
norm=lambda s:' '.join(h['strip'](s).split())
files=[];inventory={}
for path in C['population']:
 sources={side:(OUT/'inputs'/side/(path+'.txt')).read_text() for side in ['base','head']}
 chunks={side:list(ns['chunks'](src)) for side,src in sources.items()}
 rows={side:{name:dict(private=private,text=text,header=header(text)) for name,private,text in chunks[side]} for side in ['base','head']}
 assert all(len(rows[side])==len(chunks[side]) for side in ['base','head'])
 a,b=rows['base'],rows['head'];common=a.keys()&b.keys()
 changed_headers=[dict(name=n,base=a[n]['header'],head=b[n]['header']) for n in sorted(common) if a[n]['header']!=b[n]['header']]
 visibility=[n for n in sorted(common) if a[n]['private']!=b[n]['private']]
 pubA=[n for n,priv,t in chunks['base'] if not priv];pubB=[n for n,priv,t in chunks['head'] if not priv]
 assert not changed_headers and not visibility and pubA==pubB,path
 assert [n for n,priv,t in chunks['base'] if n in common]==[n for n,priv,t in chunks['head'] if n in common],path
 changed=[n for n in sorted(common) if norm(a[n]['text'])!=norm(b[n]['text'])]
 added=[n for n,priv,t in chunks['head'] if n not in a];removed=[n for n,priv,t in chunks['base'] if n not in b]
 assert not removed,path
 assert all(b[n]['private'] for n in added),path
 if path.endswith('/Hierarchy.lean'):
  assert changed==['Complexity.space_universal'] and len(added)==18
  assert all(n.startswith('Complexity.f6_') for n in added)
 else: assert not changed and not added and sources['base']==sources['head'],path
 termrows={}
 for side in ['base','head']:
  termrows[side]={n:norm(r['text']) for n,r in rows[side].items() if not re.search(r'\b(?:theorem|lemma)\b',r['header'])}
 assert termrows['base']==termrows['head'],path
 attrs={side:[s for s in sources[side].splitlines() if re.match(r'^\s*(?:@\[|attribute\b)',s)] for side in ['base','head']}
 assert attrs['base']==attrs['head'],path
 imports={side:[s for s in sources[side].splitlines() if re.match(r'^\s*import\s',s)] for side in ['base','head']}
 assert imports['base']==imports['head'],path
 row=dict(path=path,base_source_declarations=len(a),head_source_declarations=len(b),public_order_names_visibility_identical=True,
  all_common_complete_headers_identical=True,all_common_relative_order_identical=True,private_added=added,removed=removed,
  changed_common_code_chunks=changed,source_terms_bodies_identical=True,source_term_count=len(termrows['head']),attributes_identical=True,imports_identical=True,
  type_let_headers=[dict(name=n,header=b[n]['header']) for n in sorted(b) if re.search(r'\blet(?:I)?\b',b[n]['header'])])
 files.append(row)
 inventory[path]={side:[dict(name=n,private=p,header=rows[side][n]['header'],chunk_sha256=sha(t.encode()),normalized_code_sha256=sha(norm(t).encode())) for n,p,t in chunks[side]] for side in ['base','head']}
save('source-inventory-complete-headers.json',inventory)
save('source-preservation.json',dict(base=C['base'],head=C['head'],method='Canonical qualified declaration chunks with reviewed bracket-aware delimiter additionally skipping top-level type let/letI initializer assignments. All four Python controls passed. Source-only; no Lean AST, compiled/generated census, macro or notation claim.',all23_public_headers_names_visibility_order_preserved=True,only_existing_code_change='Complexity.space_universal',new_private_helpers=18,all23_source_terms_imports_attributes_preserved=True,files=files))

tools={'style':('scripts/style_lint.py','e7f8da764a22bd61c3b2cecca7920436f20bf172d24c81648cfee81a5862c144'),
       'campaign':('scripts/campaign_style_lint.py','65c420ea2f33165c674c13bf181995543133cd4b63290631655e31a4b3b29e2e')}
results={'base':{},'head':{}}
for label,(tool,digest) in tools.items():
 data=(ROOT/tool).read_bytes();assert sha(data)==digest
 for pin in [C['base'],C['head']]:assert subprocess.run(['git','-C',str(ROOT),'show',pin+':'+tool],check=True,stdout=subprocess.PIPE).stdout==data
 (OUT/'tools'/(Path(tool).name+'.txt')).write_bytes(data)
 for side in ['base','head']:
  tree=Path(C['temporary_trees'][side]);target=tree/tool;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  command=['python3','-I',str(target)]+(list(C['population']) if label=='style' else ['TCSlib','--check8b'])
  start=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.time()
  q=subprocess.run(command,cwd=tree,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  (OUT/(label+'-'+side+'.out')).write_bytes(q.stdout);(OUT/(label+'-'+side+'.stderr.out')).write_bytes(q.stderr)
  if label=='style':
   findings=[s for s in q.stdout.decode().splitlines() if s.strip()];counts={'findings':len(findings)}
   assert str(len(findings))+' findings in 23 files' in q.stderr.decode()
  else:
   findings=[s for s in q.stdout.decode().splitlines() if re.match(r'^(?:FAIL|WARN|INFO)\s',s)]
   counts={k:sum(s.startswith(k) for s in findings) for k in ['FAIL','WARN','INFO']};assert 'over 23 files' in q.stdout.decode()
  receipt=dict(command=command,cwd=str(tree),start_utc=start,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.time()-tick,exit=q.returncode,stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr),counts=counts,findings=findings)
  save(label+'-'+side+'-run.json',receipt);results[side][label]=receipt
normalize=lambda s:re.sub(r'\bline \d+\b','line <LINE>',re.sub(r'\b\d+ lines\b','<LINES> lines',re.sub(r':\d+:',':LINE:',s)))
delta={}
for label in tools:
 a={normalize(s) for s in results['base'][label]['findings']};b={normalize(s) for s in results['head'][label]['findings']}
 delta[label]=dict(normalized_new=sorted(b-a),normalized_gone=sorted(a-b))
save('lint-results.json',dict(method='Fresh unmodified canonical CLIs on the same complete23 captured source exports, both BASE and HEAD. No old21 metrics substituted. Diagnostic normalization only source line offsets/counts, not content.',sides=results,delta=delta))
print(json.dumps(dict(source_preservation='PASS',private_added=18,existing_changed=['Complexity.space_universal'],lints={s:{k:r['counts'] for k,r in v.items()} for s,v in results.items()},delta=delta),indent=2))
