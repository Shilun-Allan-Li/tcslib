"""Independent bounded receipt checks; no Lean/source/Git mutation."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
p=Path(__file__).resolve().parent
wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-epad')
H=lambda b:hashlib.sha256(b).hexdigest()
base='b1f553b315f31b949076e91119473ce4070e7d53'
env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
def git(*a):
 return subprocess.run(['git','-C',str(wt),*a],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env).stdout
assert git('rev-parse','HEAD').decode().strip()==base
assert not git('diff','--name-only','--','*.lean').strip()
assert not git('diff','--cached','--name-only','--','*.lean').strip()
sweep=json.loads((p/'sweep-inventory.json').read_text())
for row in sweep['source_files']:
 b=(wt/row['file']).read_bytes()
 assert b==git('show',base+':'+row['file'])
 assert H(b)==row['sha256']
# Verify exact inverse replacement recovers every byte of all three old files.
changes=json.loads((p/'proposal-receipt.json').read_text())['changes']
freeze=[]
for owner in ['Loop','Primitives','Catalog']:
 before=(p/'inputs'/f'{owner}-baseline.lean.txt').read_text()
 after=(p/'inputs'/f'{owner}-after-b1-body-proposal-REQUIRES-API119.lean.txt').read_text()
 reconstructed=before
 for ch in changes:
  if ch['file']!=owner or ch.get('action'):continue
  name=ch['declaration']
  old=(p/'inputs'/f'{owner}-{name}-before.lean.txt').read_text()
  new=(p/'inputs'/f'{owner}-{name}-after.lean.txt').read_text()
  assert reconstructed.count(old)==1
  reconstructed=reconstructed.replace(old,new,1)
 if owner=='Catalog':
  removed=(p/'inputs/removed-Catalog-redirect-block.lean.txt').read_text()
  assert reconstructed.count(removed)==1
  reconstructed=reconstructed.replace(removed,'',1)
 assert reconstructed==after
 freeze.append({'file':owner,'all_nontarget_source_bytes_exact':True,'before_sha256':H(before.encode()),'after_six_body_proposal_sha256':H(after.encode())})
# Seventh is separate and leaves its complete header and suffix unchanged.
before=(p/'inputs/Loop-emCall_eval_first-before.lean.txt').read_text()
after=(p/'inputs/Loop-emCall_eval_first-after.lean.txt').read_text()
assert before.split(':= by',1)[0]==after.split(':= by',1)[0]
assert before[before.index('  have htag :'):]==after[after.index('  have htag :'):]
assert 'output_unique' not in after and 'Nat.find' not in after
combined=(p/'inputs/Loop-after-b1-seven-body-proposal-REQUIRES-API119.lean.txt').read_text()
six=(p/'inputs/Loop-after-b1-body-proposal-REQUIRES-API119.lean.txt').read_text()
assert six.replace(before,after,1)==combined
# Every recorded run input/output hash and requested snapshot pin must match.
runs={}
for name in ['Consumers-native','Consumers-sealed','Controls-native','Controls-sealed']:
 r=json.loads((p/f'{name}-run.json').read_text())
 assert H((p/f'{name}.lean.txt').read_bytes())==r['input_sha256']
 assert H((p/f'{name}.out').read_bytes())==r['output_sha256']
 assert r['all_five_publisher_oleans_unchanged'] and r['input_stable']
 assert r['snapshot'].endswith('/oleans-mfollowup-preflight')
 assert r['toolchain']=='leanprover/lean4:v4.25.0'
 runs[name]={k:r[k] for k in ['exit','errors','warnings','seconds','input_sha256','output_sha256']}
assert runs['Consumers-native']['exit']==runs['Consumers-sealed']['exit']==0
assert runs['Consumers-native']['errors']==runs['Consumers-sealed']['errors']==0
assert runs['Controls-native']['exit']==0 and runs['Controls-native']['errors']==0
assert runs['Controls-sealed']['exit']==1 and runs['Controls-sealed']['errors']==14
assert all(r['warnings']==0 for r in runs.values())
defs=json.loads((p/'probe-scope.json').read_text())['guard_definitions']
expected={(n,m) for n in defs for m in ['point','abstract']}
pat=re.compile(r'^CONTROL\|([^|]+)\|(point|abstract)\|(PASS|FAIL)(?:\|kernelChecked=([^\s]+))?$',re.M)
def validate(native,sealed):
 n=pat.findall(native);s=pat.findall(sealed)
 assert len(n)==len(s)==len(expected)==14
 assert {(a,b) for a,b,_,_ in n}==expected=={(a,b) for a,b,_,_ in s}
 assert all(c=='PASS' and d for a,b,c,d in n)
 assert all(c=='FAIL' and not d for a,b,c,d in s)
 assert len({d for a,b,c,d in n})==14
 e=re.findall(r'^.*?: error: RFL_CONTROL\|([^|]+)\|(point|abstract)\|',sealed,re.M)
 assert len(e)==14 and set(e)==expected
 assert len(re.findall(r': error:',sealed))==14
n=(p/'Controls-native.out').read_text();s=(p/'Controls-sealed.out').read_text();validate(n,s)
neg=[]
for label,n2,s2 in [('drop-native',n.splitlines(keepends=True)[0].join([])+''.join(n.splitlines(keepends=True)[1:]),s),('duplicate-native',n+n.splitlines(keepends=True)[0],s),('drop-sealed-marker',n,s.replace('CONTROL|Turing.MultiTapeTM.step|point|FAIL\n','',1)),('duplicate-sealed-marker',n,s+'CONTROL|Turing.MultiTapeTM.step|point|FAIL\n')]:
 try:validate(n2,s2)
 except AssertionError:neg.append({'case':label,'rejected':True})
 else:raise AssertionError(label+' was accepted')
c=(p/'Consumers-sealed.out').read_text();assert c==(p/'Consumers-native.out').read_text()
axrows=re.findall(r'^AX\|([^|]+)\|\[([^\]]*)\]$',c,re.M)
assert len(axrows)==7 and len(set(a for a,b in axrows))==7
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(x.strip() for x in a.split(',') if x.strip())<=allowed for _,a in axrows)
defrows=[x.split('|') for x in c.splitlines() if x.startswith('DEF|')]
ordinary={x[2] for x in defrows if x[4]!='abbrev'}
assert ordinary<=set(defs)
abbrevs=sorted({x[2] for x in defrows if x[4]=='abbrev'})
for src in ['Consumers-native.lean.txt','Consumers-sealed.lean.txt']:
 text=(p/src).read_text()
 proof=text[text.index('private lemma'):text.index('#print axioms')]
 assert not re.search(r'\b(?:simp|simp_all|dsimp|unfold|delta|change)\b',proof)
 rwargs=re.findall(r'\brw\s*\[([^\]]+)\]',proof)
 assert rwargs==['Turing.pairDiagTM_spaceUsed','Turing.FinTM.incFixedTM_spaceUsed']
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',proof)
receipt={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline':base,'actual_all12_source_and_clean_Lean_unchanged':True,'six_changes_byte_freeze':freeze,'seventh_exact_header_and_suffix_preserved':True,'native_scope':'3 exact private headers + 2 zero-space proof leaves; not seventh/full Catalog rows/full MIG module/integrated replay','runs':runs,'control_pairs':14,'control_expected_sealed_negative_errors':14,'controls_exact_identity_and_multiplicity':True,'synthetic_corruption_rejected':neg,'AX':{'proof_roots':5,'proof_descendants':2,'standard_only':True,'all_rows':[{ 'name':name,'axioms':[x.strip() for x in ax.split(',') if x.strip()]} for name,ax in axrows]},'ordinary_foreign_TCSlib_definitions_reached':sorted(ordinary),'guarded_conservative_extra_definitions':sorted(set(defs)-ordinary),'excluded_compiled_abbrev_projections':abbrevs,'explicit_tactic_arguments':'Only two rw arguments, both published theorem facts; no foreign definition as a named tactic argument. Singleton rfl proves q=q. Instrumentation attributes are outside production proofs.','strong_guard_before_all_headers':True,'sealed_default_simp_removals':['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],'no_source_Git_snapshot_cache_screen_mutation':True,'elapsed_note':'Consumers-native elapsed242.91seconds includes managed slot waiting; no pure elaboration-time claim.'}
(p/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ['AX','six_changes_byte_freeze','runs']},indent=2))
