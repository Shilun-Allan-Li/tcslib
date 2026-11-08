"""Prepare inert b1-based body patches only; never write an actual Lean checkout."""
from pathlib import Path
import datetime,difflib,hashlib,json,os,re,subprocess
out=Path(__file__).resolve().parent;root=out.parents[4];wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-epad');base='b1f553b315f31b949076e91119473ce4070e7d53';api='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.run(['git','-C',str(wt),*a],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,env=env).stdout
assert git('rev-parse','HEAD').decode().strip()==base
for c in [base,api]:assert git('cat-file','-t',c).strip()==b'commit'
assert not git('diff','--name-only','--','*.lean').strip()
files={}
for name in ['Loop','Primitives','Catalog']:
 path=f'TCSlib/Complexity/TuringMachine/Build/{name}.lean';b=(wt/path).read_bytes();assert b==git('show',base+':'+path);files[name]=b.decode();(out/'inputs'/(name+'-baseline.lean.txt')).write_bytes(b)
# Existing selected headers contain no top-level statement-valued let. Scan the actual
# delimiter with balanced delimiters/comments/strings instead of first textual ':='.
def delimiter(s):
 depth=0;i=0;comment=0;string=False
 while i<len(s)-1:
  if comment:
   if s.startswith('/-',i):comment+=1;i+=2
   elif s.startswith('-/',i):comment-=1;i+=2
   else:i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:i+=1
  elif s.startswith('/-',i):comment=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j+1
  elif s[i]=='"':string=True;i+=1
  elif s[i] in '([{':depth+=1;i+=1
  elif s[i] in ')]}':depth-=1;assert depth>=0;i+=1
  elif s.startswith(':=',i) and depth==0:return i
  else:i+=1
 raise AssertionError('no actual body delimiter')
def chunk(s,name,private=True):
 prefix=('private lemma ' if private else 'theorem ')+name
 a=s.index(prefix);z=s.find('\n/--',a);z=len(s) if z<0 else z+1
 raw=s[a:z];d=delimiter(raw);return a,z,raw[:d+2],raw[d+2:]
forward=' by\n  exact MultiTapeTM.exists_first_entry_of_fixed tm stop c d T hfix hd hT\n\n'
singleton=''' by
  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed tm (fun r => r = q) c d T
    (by
      rintro z ⟨r, hz, hr⟩
      subst r
      exact hfix z hz)
    ⟨q, hd, rfl⟩ hT
  refine ⟨t, ht, ?_, he⟩
  intro j hj hq
  exact hcut j hj ⟨q, hq, rfl⟩

'''
proposed=dict(files);changes=[]
for owner,name,body in [('Loop','emCall_first_entry',forward),('Primitives','catalogFirstEntry',singleton),('Primitives','emitter_first_entry',forward)]:
 s=proposed[owner];a,z,h,oldbody=chunk(s,name);new=h+body;s=s[:a]+new+s[z:];assert chunk(s,name)[2]==h;proposed[owner]=s
 changes.append({'file':owner,'declaration':name,'private':True,'header_sha256':H(h.encode()),'before_body_sha256':H(oldbody.encode()),'after_body_sha256':H(body.encode()),'full_header_bytes_preserved':True,'replacement_body':body})
 for label,data in [('before',h+oldbody),('after',new)]:(out/'inputs'/(owner+'-'+name+'-'+label+'.lean.txt')).write_text(data)
assert 'f2_catalogFirstEntry' not in files['Catalog']
for name,fact in [('computesFunInTime_pairDup_spaceUsed','pairDiagTM_spaceUsed'),('computesFunInTime_incFixed_spaceUsed','incFixedTM_spaceUsed')]:
 s=proposed['Catalog'];a,z,h,b=chunk(s,name,False);old='rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]';assert b.count(old)==1;nb=b.replace(old,'rw ['+fact+']');proposed['Catalog']=s[:a]+h+nb+s[z:]
 assert chunk(proposed['Catalog'],name,False)[2]==h
 changes.append({'file':'Catalog','declaration':name,'private':False,'header_sha256':H(h.encode()),'before_body_sha256':H(b.encode()),'after_body_sha256':H(nb.encode()),'full_header_bytes_preserved':True,'witness_and_time_coefficient_unchanged':True,'replacement_leaf':'rw ['+fact+']; omega'})
 for label,data in [('before',h+b),('after',h+nb)]:(out/'inputs'/('Catalog-'+name+'-'+label+'.lean.txt')).write_text(data)
# Delete only the duplicate existing block; its global public name is supplied by API119 Wrappers.
s=proposed['Catalog'];a,z,h,b=chunk(s,'redirectTM_spaceUsedByTape',False);start=s.rfind('/--',0,a);block=s[start:z];approved=(root/'campaign/gates/119-mig1-followup-api/source/approved-moved-block.lean.txt').read_text();assert block==approved
assert approved in git('show',api+':TCSlib/Complexity/TuringMachine/Build/Wrappers.lean').decode()
proposed['Catalog']=s[:start]+s[z:];assert 'theorem redirectTM_spaceUsedByTape' not in proposed['Catalog'];(out/'inputs/removed-Catalog-redirect-block.lean.txt').write_text(block)
changes.append({'file':'Catalog','declaration':'redirectTM_spaceUsedByTape','action':'Delete exact approved1043byte block from MIGCatalog after API119 owner adoption','block_sha256':H(block.encode()),'exact_new_Wrappers_owner_block':True,'global_public_name_removed':False})
diff=''
for n in ['Loop','Primitives','Catalog']:
 assert (wt/f'TCSlib/Complexity/TuringMachine/Build/{n}.lean').read_text()==files[n]
 (out/'inputs'/(n+'-after-b1-body-proposal-REQUIRES-API119.lean.txt')).write_text(proposed[n]);diff+=''.join(difflib.unified_diff(files[n].splitlines(keepends=True),proposed[n].splitlines(keepends=True),fromfile='a/TCSlib/Complexity/TuringMachine/Build/'+n+'.lean',tofile='b/TCSlib/Complexity/TuringMachine/Build/'+n+'.lean'))
(out/'consumer-bodies.patch').write_text(diff)
receipt={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline':base,'actual_MIG_HEAD_and_clean_Lean_checked':True,'API_statement_source':api,'target_publisher_snapshot':'oleans-mfollowup-preflight read-only; no mutable replay snapshot read','status':'Inert proposed b1-relative consumer delta only; do NOT overwrite files after merge with saved b1-based whole-source copies','no_actual_source_Git_cache_snapshot_screen_or_compilation_action':True,'changes':changes,'source_hashes':[{'file':f'TCSlib/Complexity/TuringMachine/Build/{n}.lean','baseline_sha256':H(files[n].encode()),'after_body_proposal_sha256':H(proposed[n].encode())} for n in ['Loop','Primitives','Catalog']],'f2_catalogFirstEntry_already_absent':True,'public_headers_imports_runtime_defs_machine_tables_and_callers_unchanged_except_intended_duplicate_decl_removal':True,'private_names_headers_decidability_binders_and_caller_sites_retained':True,'no_new_public_or_private_declaration':True,'Catalog_witnesses_and_time_constants':'pairDiagTM/6 and incFixedTM/3 unchanged','integration_prerequisite':'Gate119 closes and Seyoon merges#234; root first integrates its complete source then applies only these scoped body/deletion hunks, preserving all API119 publisher additions.'};(out/'proposal-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ['changes']},indent=2))
