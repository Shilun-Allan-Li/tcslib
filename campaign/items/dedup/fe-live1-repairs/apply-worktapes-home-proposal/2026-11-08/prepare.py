from pathlib import Path
import os,subprocess,json,hashlib,tempfile,tarfile,io,ast,re,difflib,datetime,shutil
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest();src=G('rev-parse','origin/pr/251^{commit}').decode().strip();G('cat-file','-e',src+'^{commit}');assert src=='0f926779de590194f5222277dc038d2ad097ff91'
RT=Path(tempfile.mkdtemp(prefix='ab34-apply-worktapes-home-runtime-',dir='/private/tmp'));W=RT/'source';W.mkdir();S=Path(os.environ['TCSLIB_SCRATCH'])/'oleans-mac8';OV=RT/'objects'
raw=G('archive',src,'TCSlib','TCSlib.lean','lean-toolchain','lake-manifest.json','lakefile.lean')
with tarfile.open(fileobj=io.BytesIO(raw)) as tar:
 for member in tar.getmembers():assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
 tar.extractall(W,filter='data')
(W/'.lake').mkdir();(W/'.lake/packages').symlink_to(Path(os.environ['TCSLIB_REPO'])/'.lake/packages',target_is_directory=True)
helper=R/'devtools/seyoon/declfreeze.py';t=ast.parse(helper.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),'canonical_parser','exec'),ns)
paths=['TCSlib/Complexity/TuringMachine/Configuration.lean','TCSlib/Complexity/TuringMachine/Simulation.lean'];base={p:(W/p).read_text() for p in paths};chunk={n:c for n,p,c in ns['chunks'](base[paths[1]])}['Turing.Action.apply_workTapes'];assert base[paths[1]].count(chunk)==1
cand=dict(base);cand[paths[1]]=cand[paths[1]].replace(chunk+'\n','',1)
needle='attribute [simps (config := { isSimp := false }) state inputPos workTapePos output] Action.apply';assert cand[paths[0]].count(needle)==1;cand[paths[0]]=cand[paths[0]].replace(needle,needle+'\n\n'+chunk,1)
(O/'source').mkdir();bindings=[]
for p in paths:
 for label,data in [('BASE',base[p]),('CANDIDATE',cand[p])]:
  q=O/'source'/label/(p+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(data)
 b=G('rev-parse',src+':'+p).decode().strip();G('cat-file','-e',b);bindings.append({'path':p,'source':src,'BASE_Git_blob':b,'BASE_SHA256':H(base[p].encode()),'CANDIDATE_SHA256':H(cand[p].encode()),'imports_exact':re.findall(r'^import .+$',base[p],re.M)==re.findall(r'^import .+$',cand[p],re.M),'all_unchanged_text_exact_after_inverse_edit':(cand[p].replace(chunk+'\n','',1)==base[p] if p==paths[0] else cand[p].replace('namespace Turing\n\n','namespace Turing\n\n'+chunk+'\n',1)==base[p])})
# A full inverse move, rather than a permissive diff, establishes that no old byte was otherwise touched.
inverse={p:cand[p] for p in paths};inverse[paths[0]]=inverse[paths[0]].replace(needle+'\n\n'+chunk,needle,1);old_marker='namespace Turing\n\n';assert inverse[paths[1]].count(old_marker)==1;inverse[paths[1]]=inverse[paths[1]].replace(old_marker,old_marker+chunk+'\n',1)
assert inverse==base
for p in paths:bindings[paths.index(p)]['all_unchanged_text_exact_after_inverse_edit']=True
patch=''.join(''.join(difflib.unified_diff(base[p].splitlines(True),cand[p].splitlines(True),fromfile='a/'+p,tofile='b/'+p)) for p in paths);(O/'PROPOSED-EXACT-MOVE.patch').write_text(patch);(O/'MOVED-CHUNK.lean.txt').write_text(chunk+'\n')
countbase=sum(1 for p in paths for n,pr,c in ns['chunks'](base[p]) if n=='Turing.Action.apply_workTapes');countcand=sum(1 for p in paths for n,pr,c in ns['chunks'](cand[p]) if n=='Turing.Action.apply_workTapes');assert countbase==countcand==1
(O/'SOURCE-FREEZE.json').write_text(json.dumps({'source':src,'reader':'Turing.Action.apply_workTapes','chunk_SHA256_without_capture_LF':H(chunk.encode()),'bindings':bindings,'exact_complete_doc_name_statement_proof_move':True,'inverse_move_recovers_all_original_owner_bytes':True,'source_declaration_counts_BASE_CANDIDATE':[countbase,countcand],'all_old_imports_headers_definitions_attributes_preserved':True,'old_Simulation_namespace_wrapper_preserved':True,'old_Configuration_header_API_prose_still_says_Simulation_preserved_deliberately':True,'only_private_extracted_source_experiment_no_checkout_adoption':True},indent=2)+'\n')
# Record all 895 physical input objects before creating one complete private clone.
objects=[]
for f in sorted(S.rglob('*.olean')):objects.append({'path':str(f.relative_to(S)),'bytes':f.stat().st_size,'SHA256':H(f.read_bytes())})
assert len(objects)==895
(O/'INPUT895-original-before.json').write_text(json.dumps(objects,indent=2)+'\n');subprocess.run(['cp','-cR',str(S),str(OV)],check=True)
clones=[]
for f in sorted(OV.rglob('*.olean')):clones.append({'path':str(f.relative_to(OV)),'bytes':f.stat().st_size,'SHA256':H(f.read_bytes())})
assert clones==objects
(O/'INPUT895-clone-before.json').write_text(json.dumps(clones,indent=2)+'\n')
context={'source':src,'runtime':str(RT),'private_source_tree':str(W),'whole_input_snapshot':str(S),'private_complete_clone':str(OV),'input_physical_olean_count':895,'clone_all_895_objects_exact_at_start':True,'packages_symlink':str(W/'.lake/packages'),'packages_target':str((W/'.lake/packages').resolve()),'lean_toolchain':(W/'lean-toolchain').read_text().strip(),'lean_toolchain_SHA256':H((W/'lean-toolchain').read_bytes()),'lake_manifest_SHA256':H((W/'lake-manifest.json').read_bytes()),'TCSLIB_LEAN_SLOTS':os.environ.get('TCSLIB_LEAN_SLOTS'),'approved_helper_paths':{n:str(R/'devtools/seyoon'/n) for n in ['leanelab.sh','leanelab-o.sh']},'approved_helper_SHA256':{n:H((R/'devtools/seyoon'/n).read_bytes()) for n in ['leanelab.sh','leanelab-o.sh']},'started_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(O/'CONTEXT.json').write_text(json.dumps(context,indent=2)+'\n');print(json.dumps(context,indent=2))
