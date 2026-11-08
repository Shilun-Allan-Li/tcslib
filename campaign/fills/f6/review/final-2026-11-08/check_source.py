"""Source-only freeze/patch/Git-data validation in a private quarantine; never adopt source."""
from pathlib import Path
import ast,datetime,hashlib,importlib.util,json,os,re,subprocess,sys,tempfile
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];info=json.loads((out/'ingestion.json').read_text());scratch=Path(info['scratch_root']);base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';file='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean';H=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
commands=[];env=dict(os.environ,GIT_OPTIONAL_LOCKS='0',GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL='/dev/null',GIT_TERMINAL_PROMPT='0',GIT_PAGER='cat')
def run(cmd):
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env)
 commands.append({'command':cmd,'exit':p.returncode,'stdout':p.stdout.decode('utf-8',errors='replace'),'stderr':p.stderr.decode('utf-8',errors='replace')})
 assert p.returncode==0,(cmd,p.stderr.decode());return p.stdout
common=Path(run(['git','-C',str(root),'rev-parse','--git-common-dir']).decode().strip())
if not common.is_absolute():common=(root/common).resolve()
q=scratch/'quarantine.git';q.mkdir(mode=0o700);empty=scratch/'empty-template';empty.mkdir(mode=0o700)
run(['git','-c','core.hooksPath=/dev/null','-c','gc.auto=0','-c','maintenance.auto=false','init','--bare','--initial-branch=quarantine','--template='+str(empty),str(q)])
(q/'objects/info/alternates').write_text(str(common/'objects')+'\n')
# All object writes stay inside this fresh bare ODB. Alternates only read campaign objects.
env['GIT_OBJECT_DIRECTORY']=str(q/'objects');env['GIT_ALTERNATE_OBJECT_DIRECTORIES']=str(common/'objects')
def git(*a):return run(['git','--git-dir='+str(q),'-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-c','gc.auto=0','-c','maintenance.auto=false',*a])
base=git('rev-parse','--verify',base+'^{commit}').decode().strip();git('cat-file','-e',base+'^{commit}')
base_source=git('show',base+':'+file).decode();assert H(base_source)=='1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f'
(out/'base-Hierarchy.lean.txt').write_text(base_source)
heads={};bundle_rows=[]
for row in info['deliveries']:
 label=row['label'];d=scratch/label;bundle=d/'fill-f6-space-universal.bundle'
 git('bundle','verify',str(bundle));git('bundle','unbundle',str(bundle))
 head=git('rev-parse','--verify',row['head_as_supplied']+'^{commit}').decode().strip();git('cat-file','-e',head+'^{commit}');heads[label]=head
 changed=git('diff','--no-ext-diff','--no-textconv','--name-only',base,head).decode().splitlines();assert changed==[file]
 b=git('show',head+':'+file);assert H(b)==row['owned_source_sha256'] and b==(out/f'{label}-Hierarchy.lean.txt').read_bytes()
 bundle_rows.append({'label':label,'head':head,'actual_Git_bundle_verified_and_unbundled_only_into_private_quarantine':True,'full_commit_object_revparse_catfile_verified':True,'all_base_to_head_changed_paths':changed,'exact_Git_blob_equals_delivered_source':True,'source_sha256':H(b)})
assert not git('for-each-ref').strip(),'unbundle must not install refs'
# Apply every delivered textual hunk ourselves without running git apply/payload tools.
def patch(text,old):
 lines=text.splitlines(keepends=True);i=0;paths=[];result=old.splitlines(keepends=True)
 while i<len(lines):
  m=re.match(r'diff --git a/(\S+) b/(\S+)\n',lines[i])
  if not m:i+=1;continue
  a,b=m.groups();assert a==b==file;paths.append(a);i+=1;new=[];pos=0;hunks=0
  while i<len(lines) and not lines[i].startswith('diff --git '):
   m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
   if not m:i+=1;continue
   start,n,to,made=[int(v) if v is not None else 1 for v in m.groups()];i+=1;assert start-1>=pos;new+=result[pos:start-1];pos=start-1;assert len(new)==to-1;used=produced=0;hunks+=1
   while used<n or produced<made:
    line=lines[i];i+=1;tag=line[0];assert tag in ' +-'
    if tag in ' -':assert result[pos]==line[1:],(pos+1,result[pos],line);pos+=1;used+=1
    if tag in ' +':new.append(line[1:]);produced+=1
   assert used==n and produced==made
  assert hunks;new+=result[pos:];result=new
 assert paths==[file];return ''.join(result)
state=base_source;patches=[];last=base
for f in sorted((scratch/'final/patches').glob('0*.patch')):
 text=f.read_text();m=re.match(r'From ([0-9a-f]{40}) ',text);assert m;head=m[1];actual=git('rev-parse','--verify',head+'^{commit}').decode().strip();assert actual==head
 assert git('rev-parse',head+'^').decode().strip()==last
 state=patch(text,state);assert state.encode()==git('show',head+':'+file)
 patches.append({'patch':f.name,'full_commit':head,'source_sha256':H(state),'all_hunks_and_actual_commit_source_equal':True});last=head
assert len(patches)==6 and last==heads['final']
assert patch((scratch/'final/patches/cumulative-fill-f6-final.diff').read_text(),base_source)==state
for label in ['cp01','cp02']:
 upto=1 if label=='cp01' else 2;check=base_source
 for f in sorted((scratch/label/'patches').glob('0*.patch')):check=patch(f.read_text(),check)
 assert check==(out/f'{label}-Hierarchy.lean.txt').read_text() and heads[label]==patches[upto-1]['full_commit']
# Reviewed maintainer-owned parser; only pure split_header AST is executed, no delivery tools.
parser=root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py';sp=importlib.util.spec_from_file_location('maintainer_parser',parser);P=importlib.util.module_from_spec(sp);sp.loader.exec_module(P)
qa=root/'campaign/fills/mig1/landing/review-final-source-final/source_review.py';fn=next(n for n in ast.parse(qa.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='split_header');ns={'P':P,'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(qa),'exec'),ns);split=ns['split_header'];P.header=lambda s:P.norm(split(s)[0])
controls=[('theorem n (h : P (input := x)) : True := by\n trivial\n','True'),('theorem x :\n let y := f\n P y := by\n exact h\n','P y'),('theorem q :\n let x : T := by\n   have h := p\n   exact z h\n P x := by\n exact h\n','P x')]
for t,last in controls:assert split(t)[0].endswith(last) and split(t)[1]==':='
def declarations(text):
 ds=P.decls(text)
 for d in ds:
  raw=d['raw'];doc=re.search(r'(?m)^/(?:--|-!)',raw)
  if doc:raw=raw[:doc.start()]
  d['raw']=raw.rstrip()+'\n';d['header_raw'],d['delimiter'],d['body']=split(d['raw'])
 return ds
old=declarations(base_source);new=declarations(state);a={d['name']:d for d in old};b={d['name']:d for d in new};added=[d for d in new if d['name'] not in a]
assert len(added)==18 and all(d['private'] and d['kind']=='theorem' and d['name'].startswith('Complexity.f6_') for d in added)
assert not set(a)-set(b);assert [d['name'] for d in old]==[d['name'] for d in new if d['name'] in a]
changed=[]
for name,x in a.items():
 y=b[name];assert (x['header_raw'],x['private'],x['kind'])==(y['header_raw'],y['private'],y['kind'])
 if x['raw']!=y['raw']:changed.append(name)
assert changed==['Complexity.space_universal'];assert P.imports(base_source)==P.imports(state)
assert sum(not d['private'] for d in old)==sum(not d['private'] for d in new)==4
assert (sum(d['private'] for d in old),sum(d['private'] for d in new))==(43,61)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|set_option|macro|elab)\b',P.clean(''.join(d['raw'] for d in added)+b['Complexity.space_universal']['body']))
for label in ['cp01','cp02']:
 d=next(d for d in declarations((out/f'{label}-Hierarchy.lean.txt').read_text()) if d['name']=='Complexity.space_universal');assert d['header_raw']==a['Complexity.space_universal']['header_raw'] and re.search(r'\bsorry\b',P.clean(d['body']))
# Removing the18new chunks and restoring target leaves only authorized prose deltas.
recovered=state
for d in reversed(added):assert recovered.count(d['raw'])==1;recovered=recovered.replace(d['raw'],'',1)
assert recovered.count(b['Complexity.space_universal']['raw'])==1;recovered=recovered.replace(b['Complexity.space_universal']['raw'],a['Complexity.space_universal']['raw'],1)
import difflib
(out/'remaining-authorized-prose.diff').write_text(''.join(difflib.unified_diff(base_source.splitlines(keepends=True),recovered.splitlines(keepends=True),fromfile='base',tofile='recovered-after-removing-new-proofs')))
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Independent source/patch/freeze/Git-data review; no worktree/source checkout, real-repo refs, Lean or cache mutation','base':base,'heads':heads,'quarantine':str(q),'real_campaign_objects_alternate_readonly':str(common/'objects'),'empty_template_hooks_disabled_no_refs':True,'bundles':bundle_rows,'six_patches_exact_actual_commit_chain':patches,'cumulative_diff_exact':True,'checkpoint_sources_exact_first1and2commits':True,'source_public':[4,4],'source_private':[43,61],'added_private':[{'name':d['name'],'line':d['start'],'header_sha256':H(d['header_raw']),'body_sha256':H(d['body'])} for d in added],'only_changed_old_declaration':'Complexity.space_universal','all_old_headers_kinds_visibility_homes_imports_relative_order_and_othertheorem_definition_chunks_frozen':True,'all_new_source_no_admit_axiom_unsafe_elab_or_macro':True,'cp01_cp02_original_target_still_admitted':True,'final_target_source_filled':True,'balanced_full_header_controls_pass':True,'target_header_sha256_literal_start_including_delimiter':H(b['Complexity.space_universal']['raw'].split(':= by',1)[0]),'final_source_sha256':H(state),'limits':'This verifies Git objects and source, not a fresh native proof, seal, compiled census, or merged-tree replay. Delivery source not adopted.'}
(out/'source-freeze.json').write_text(json.dumps(result,indent=2)+'\n');(out/'quarantine-commands.json').write_text(json.dumps(commands,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['added_private','six_patches_exact_actual_commit_chain','bundles']},indent=2))
