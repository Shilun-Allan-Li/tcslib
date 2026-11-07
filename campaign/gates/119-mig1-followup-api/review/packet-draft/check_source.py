"""Read-only exact source linkage for the gate119 packet draft."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess
out=Path(__file__).resolve().parent;root=out.parents[4];gate=root/'campaign/gates/119-mig1-followup-api';base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';api='1160c18f03fd318f0dec25738790935fa61379d4';head='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.run(['git','-C',str(root),*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,env=env).stdout
for c in [base,api,head]:assert git('cat-file','-t',c).strip()==b'commit'
assert not git('diff','--name-only',api,base,'--','*.lean').strip()
assert not git('diff','--name-only','626b1a81ddd33f4b0e0dabd4e874a16a0fe71724',head,'--','*.lean').strip()
subprocess.run(['git','-C',str(root),'merge-base','--is-ancestor',base,head],check=True,env=env)
changed=git('diff','--name-only',base,head,'--','*.lean').decode().splitlines();expected=sorted(['TCSlib/Complexity/TuringMachine/'+x+'.lean' for x in ['Finite','Encoding','Build/Wrappers','Build/Primitives','Build/Catalog']]);assert sorted(changed)==expected
pop=(gate/'review/source-lint-screen/population.txt').read_text().splitlines();assert len(pop)==len(set(pop))==16
rows=[]
for path in pop:
 b=git('show',base+':'+path);h=git('show',head+':'+path)
 for side,data in [('base',b),('head',h)]:assert data==(gate/'review/source-lint-screen/inputs'/side/(path+'.txt')).read_bytes()
 rows.append({'path':path,'base_sha256':H(b),'head_sha256':H(h),'both_captured_screen_inputs_exact_at_current_pins':True,'changed':path in changed})
pre=json.loads((gate/'evidence/preflight/receipt.json').read_text());assert pre['failures']==0
assert all(H(git('show',head+':'+r['source']))==r['source_sha256'] for r in pre['runs'])
freeze=json.loads((gate/'source/whole-source-freeze.json').read_text());assert all(H(git('show',head+':'+r['path']))==r['after_sha256'] and H(git('show',base+':'+r['path']))==r['before_sha256'] for r in freeze['source_scope'])
result={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Source-only object/capture linkage; no native/screen execution or Git/source mutation.','base':base,'API_metadata_baseline':api,'head':head,'source_byte_reference':'626b1a81ddd33f4b0e0dabd4e874a16a0fe71724','full_Lean_difference_source_reference_to_current_head_empty':True,'commit_objects_verified':True,'base_ancestor_of_head':True,'full_Lean_difference_API_to_base_empty':True,'changed_Lean_files_exactly_five':changed,'all_five_actual_native_preflight_source_hashes_equal_current_head':True,'all_five_whole_source_freeze_pairs_equal_current_base_head':True,'full16_base_head_screen_source_captures_equal_current_pins':rows,'records_bundle_pin':'PENDING ROOT FINALIZATION','full401_replay':'PENDING ROOT ADOPTION','full16_screen_head_and_semantic_disposition':'PENDING C/ROOT ADOPTION'};(out/'source-linkage.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='full16_base_head_screen_source_captures_equal_current_pins'},indent=2))
