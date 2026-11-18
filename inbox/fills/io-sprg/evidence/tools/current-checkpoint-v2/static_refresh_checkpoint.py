# io-sprg read-only source/evidence checks, Mac root 2026-11-18.
# No Lean; campaign totals separated from individual FAIL/WARN findings.
from pathlib import Path
import hashlib,json,subprocess,re,datetime,argparse,runpy,os
ap=argparse.ArgumentParser();ap.add_argument('--inventory',required=True)
ap.add_argument('--build',required=True);ap.add_argument('--freeze-check',required=True)
ap.add_argument('--environment-tree',required=True)
ap.add_argument('--out',required=True);ap.add_argument('--require-complete',action='store_true');a=ap.parse_args()
iv=runpy.run_path(str(Path(__file__).with_name('checkpoint_inventory.py')))
inventory=iv['load'](a.inventory);p=Path(inventory['root']);os.chdir(p)
base=inventory['base'];head=inventory['head'];out=Path(a.out).resolve();assert not out.exists()
out.mkdir(parents=True);files=iv['files'](inventory);files2=sorted(inventory['changed_paths'])
frozen=json.loads(Path(a.freeze_check).read_text())
assert frozen['status']=='FROZEN_GLOBAL_HEADERS_AND_STATEMENT_PROSE_PASS'
assert set(frozen['current_source_sha256'])==set(files)
assert all(frozen['current_source_sha256'][f]==inventory['source_sha256'][f] for f in files)

checks={}
for name,cmd in [('decls2',['python3','-I','evidence/tools/seal/decls2.py','.',base,*files2]),('style',['python3','-I','scripts/style_lint.py',*files]),('sk15',['python3','-I','evidence/tools/dev/sk15.py',*files]),('clash',['python3','-I','evidence/tools/clash/clash_scan.py','.',base,head,str(out/'clash')]),('campaign',['python3','-I','scripts/campaign_style_lint.py','TCSlib/Cryptography','--check8b'])]:
 r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/(name+'.log')).write_text(r.stdout);print(name,'rc',r.returncode,'bytes',len(r.stdout));checks[name]=dict(rc=r.returncode,log_sha256=hashlib.sha256(r.stdout.encode()).hexdigest())
 if name!='campaign':assert r.returncode==0
base_lines=set((p/'evidence/lint/campaign-base.log').read_text().splitlines());head_lines=set((out/'campaign.log').read_text().splitlines());new=[s for s in sorted(head_lines-base_lines) if re.search(r'\b(?:FAIL|WARN)\b',s) and not s.startswith('style_lint:')];assert not new,new
(out/'campaign-diff.json').write_text(json.dumps(dict(head=head,new_fail_warn=new),indent=1)+'\n')
counts={}
for s in (out/'decls2.log').read_text().splitlines():
 if s.startswith(('ADDED\t','CHANGED\t','REMOVED\t')):counts[s.split('\t')[0]]=counts.get(s.split('\t')[0],0)+1
assert counts.get('CHANGED',0)==counts.get('REMOVED',0)==0,counts
header_parser=runpy.run_path(str(Path(__file__).with_name('freeze_global.py')))
lex=header_parser['parser_functions'](p/'evidence/tools/seal/decls2.py',{'strip','decls'},{'KW'})
names=[]
for f in files:names.extend(lex['decls']((p/f).read_text()))
assert len(names)==len(set(names)),'duplicate current public source name'
added=[l.split('\t')[2] for l in(out/'decls2.log').read_text().splitlines() if l.startswith('ADDED\t')]
assert len(added)==len(names) and set(added)==set(names),'decls2/current global name census differs'
rows=[]
for f in files:
 b=(p/f).read_bytes();ls=b.decode().splitlines();assert len(ls)<=1000 and max(map(len,ls),default=0)<=100;assert b==subprocess.check_output(['git','show',head+':'+f]);rows.append(dict(file=f,lines=len(ls),max_width=max(map(len,ls),default=0),sha256=hashlib.sha256(b).hexdigest()))
(out/'sizes-widths.json').write_text(json.dumps(dict(head=head,files=rows),indent=1)+'\n')
build=Path(a.build).resolve();expected={f[:-5] for f in files};latest={}
for line in(build/'results.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'module' not in r:continue
 if iv['owner_path'](r['module']+'.lean'):assert r['module'] in expected,'build owner outside inventory'
 if r['module'] in expected:latest[r['module']]=r
assert set(latest)==expected,'owned build key set differs'
rs=[latest[f[:-5]] for f in files];lines=['HEAD '+head,'OWNERS '+str(len(expected))]
for r in rs:
 f=r['module']+'.lean';b=(p/f).read_bytes();log=build/'mods'/(r['module'].replace('/','_')+'.log')
 assert hashlib.sha256(b).hexdigest()==r['source_sha256']==inventory['source_sha256'][f]
 assert hashlib.sha256(log.read_bytes()).hexdigest()==r['log_sha256']
 assert r['rc']==r['errors']==r['error_forms']==0
 object_path=Path(a.environment_tree)/(r['module']+'.olean')
 assert object_path.is_file() and hashlib.sha256(object_path.read_bytes()).hexdigest()==r['object_sha256'],'current compiled object differs from latest checked build'
 assert not re.search(r'error[:(]',log.read_text()),'independent error form found'
 assert not [s for s in log.read_text().splitlines() if 'warning:' in s and 'sorry' not in s]
 if a.require_complete:assert "declaration uses 'sorry'" not in log.read_text(),'final source sorry warning'
 lines.append(f"{r['module']} rc=0 errors_colon=0 errors_paren=0 source={r['source_sha256']} HEAD_match=True log={log}")
(out/'build-summary.txt').write_text('\n'.join(lines)+'\n')
(out/'frozen-file-diff.txt').write_text(subprocess.check_output(['git','diff','--stat',base,head],text=True))
changed=subprocess.check_output(['git','diff','--name-only',base,head],text=True).splitlines();assert set(changed)==set(files2)
forbidden=[];coin=[];choice=[];sampler=[];realizers=[];contract=[]
for f in files:
 for i,line in enumerate((p/f).read_text().splitlines(),1):
  if line.startswith('import '):
   imp=line.split()[1]
   if any(imp.startswith(q) for q in ['TCSlib.Programs','TCSlib.Complexity.RAMSimulation','TCSlib.Cryptography.Games.Closeness','TCSlib.Cryptography.CoinSampling.']) and imp not in ['TCSlib.Cryptography.CoinSampling.Contract','TCSlib.Cryptography.CoinSampling.Efficiency']:forbidden.append([f,i,line])
   if imp.startswith('TCSlib.Cryptography.CoinSampling.'):
    coin.append([f,i,line]);assert f in ['TCSlib/Cryptography/Obfuscation/StructuredSeed/'+n+'.lean' for n in ['Defs','BoolPRG','LPN','Targets']]
   assert not any(x in imp for x in ['DyadicLinearAlgebra','DyadicArithmetic','Encoding.BinaryArith','ClassP.BinaryArith'])
  if any(q in line for q in ['Fintype.equivFin','Classical.choose','PrimeFind']):choice.append([f,i,line])
  if re.search(r'^\s*(?:noncomputable )?def\s+(?:\w+\.)?(?:RealizesOn|RealizableOn)',line):realizers.append([f,i,line])
  if re.search(r'^\s*(?:noncomputable )?def\s+(?:\w+\.)?(?:SamplesEfficiently|DrawSamplable|CoreComputable)',line):contract.append([f,i,line])
  if 'UniformSampler' in line or 'CoinSampler' in line:sampler.append([f,i,line])
assert not forbidden and not realizers and not contract
assert not any('Fintype.equivFin' in r[2] or 'PrimeFind' in r[2] for r in choice)
for r in choice:assert r[0]=='TCSlib/Cryptography/Obfuscation/StructuredSeed/Defs.lean' and 'Classical.choose' in r[2]
for rev in [base]+subprocess.check_output(['git','rev-list','--reverse',base+'..'+head],text=True).splitlines():assert not any(f.lower().endswith('.pdf') for f in subprocess.check_output(['git','ls-tree','-r','--name-only',rev],text=True).splitlines())
assert not any(x.suffix.lower()=='.pdf' for x in (p/'evidence').rglob('*'))
committed=subprocess.check_output(['git','log','--name-only','--pretty=format:',base+'..'+head],text=True).splitlines();assert all(f.endswith('.lean') for f in committed if f)
(out/'boundary.json').write_text(json.dumps(dict(head=head,forbidden_imports=forbidden,coin_imports=coin,choice_occurrences=choice,new_realization_variants=realizers,new_contract_variants=contract,sampler_mentions=sampler,changed=changed,pdf_paths=[]),indent=1)+'\n')
envbind=runpy.run_path(str(Path(__file__).parent/'io-sprg-rule10/environment_binding.py'))
environment=envbind['snapshot'](a.environment_tree,out)
(out/'summary.json').write_text(json.dumps(dict(head=head,inventory_sha256=inventory['inventory_sha256'],environment_sha256=environment,freeze_source_hashes_match=True,checks=checks,decls=counts,owners=len(rs),lines=sum(r['lines'] for r in rows),all_widths_pass=True,new_campaign_fail_warn=new),indent=1)+'\n');print('STATIC_CHECKS_PASS',head)
