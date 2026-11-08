"""Bounded source-only twelve-file idiom enumeration; no automatic proof rewriting."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
p=Path(__file__).resolve().parent;wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-epad');base='b1f553b315f31b949076e91119473ce4070e7d53';api='1160c18f03fd318f0dec25738790935fa61379d4';env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.run(['git','-C',str(wt),*a],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,env=env).stdout
files=git('diff','--name-only',api,base,'--','*.lean').decode().splitlines();assert len(files)==12
(p/'sweep-inputs').mkdir(exist_ok=True);(p/'sweep-declarations').mkdir(exist_ok=True)
def mask(s):
 o=list(s);i=0;comment=0;string=False
 while i<len(s):
  if comment:
   if s.startswith('/-',i):o[i:i+2]='  ';comment+=1;i+=2
   elif s.startswith('-/',i):o[i:i+2]='  ';comment-=1;i+=2
   else:
    if s[i]!='\n':o[i]=' '
    i+=1
  elif string:
   if s[i]=='\\':o[i:i+2]='  ';i+=2
   elif s[i]=='"':o[i]=' ';string=False;i+=1
   else:
    if s[i]!='\n':o[i]=' '
    i+=1
  elif s.startswith('/-',i):o[i:i+2]='  ';comment=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;o[i:j]=' '*(j-i);i=j
  elif s[i]=='"':o[i]=' ';string=True;i+=1
  else:i+=1
 return ''.join(o)
D=re.compile(r'(?m)^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:lemma|theorem|def|abbrev|instance|inductive|structure)\s+([^\s({:]+)')
known={'emCall_eval_first':'seventh_existing_NONE_first_halt_proposal','emCall_first_entry':'assigned119_predicate_forward','catalogFirstEntry':'assigned119_singleton_forward','emitter_first_entry':'assigned119_predicate_forward','emCall_right_endpoint':'additional_existing_NONE_first_halt_candidate','lenStart':'additional_existing_NONE_first_halt_candidate','splitBody_count':'additional_existing_NONE_first_halt_candidate','timed_start':'additional_existing_NONE_first_halt_candidate','condTM_start':'additional_existing_NONE_first_halt_candidate','bufferedComp_start':'additional_existing_NONE_first_halt_candidate','splitEmbed_cut':'additional119_inline_live_stop_candidate','fwdMap_launch':'additional119_inline_live_stop_candidate'}
rows=[];pins=[]
for f in files:
 data=(wt/f).read_bytes();assert data==git('show',base+':'+f);s=data.decode();c=mask(s);(p/'sweep-inputs'/(f.replace('/','__')+'.txt')).write_bytes(data);pins.append({'file':f,'bytes':len(data),'sha256':H(data)})
 ds=list(D.finditer(c))
 for i,d in enumerate(ds):
  end=ds[i+1].start() if i+1<len(ds) else len(c);code=c[d.start():end];raw=s[d.start():end];flags={'Nat.find':bool(re.search(r'\bNat\.find\b',code)),'Nat.exists_eq_add_of_le':'Nat.exists_eq_add_of_le' in code,'lt_trichotomy':'lt_trichotomy' in code,'runFrom_add_and_runFrom_of_halt':'runFrom_add' in code and 'runFrom_of_halt' in code}
  if not any(flags.values()):continue
  n=d[1]
  if flags['Nat.find']:assert n in known;kind=known[n]
  elif flags['lt_trichotomy']:assert n=='compareStop_unique';kind='canonical_list_stop_uniqueness_not_TM_first_entry'
  else:kind='published_absorption_and_run_composition_context_review'
  hits=[{'line':s[:d.start()+m.start()].count('\n')+1,'term':m[0]} for m in re.finditer(r'Nat\.find(?:_min\u0027?|_spec)?|Nat\.exists_eq_add_of_le|(?:Nat\.)?lt_trichotomy|(?:MultiTapeTM\.)?runFrom_(?:add|of_halt)',code)]
  name=f'{len(rows)+1:02d}-{n.replace("\u0027","_prime").replace(".","_")}.lean.txt';(p/'sweep-declarations'/name).write_text(raw)
  rows.append({'file':f,'declaration':n,'start_line':s[:d.start()].count('\n')+1,'end_line':s[:end].count('\n')+1,'patterns':flags,'classification':kind,'full_declaration_snapshot':'sweep-declarations/'+name,'source_declaration_sha256':H(raw.encode()),'hits':hits})
assert sum(r['patterns']['Nat.find'] for r in rows)==12
result={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline':base,'scope':'All12currentMIGchangedLeanfiles; comments/strings masked; full matching declarations retained; static candidate enumeration+inspection, not semantic completeness/debt acknowledgment','source_files':pins,'matching_declarations':rows,'Nat_find_declarations':12,'Nat_exists_eq_add_of_le_declarations':sum(r['patterns']['Nat.exists_eq_add_of_le'] for r in rows),'lt_trichotomy_declarations':sum(r['patterns']['lt_trichotomy'] for r in rows),'combined_run_add_halt_declarations':sum(r['patterns']['runFrom_add_and_runFrom_of_halt'] for r in rows),'no_actual_source_or_native_screen_Git_action':True};(p/'sweep-inventory.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps([{k:r[k] for k in ['declaration','start_line','classification']} for r in rows],indent=2))
