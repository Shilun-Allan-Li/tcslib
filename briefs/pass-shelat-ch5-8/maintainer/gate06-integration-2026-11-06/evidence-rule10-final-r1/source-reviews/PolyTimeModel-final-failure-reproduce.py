"""Own read-only Git/text witness analysis for the completed PolyTimeModel probe.
No repository tools are imported or executed. Output is confined to this /tmp directory.
"""
from pathlib import Path
from collections import defaultdict
import hashlib, json, re, subprocess, difflib

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
E = MAIN / 'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1'
HIST = MAIN / 'briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r2/r6c'
BASE = 'eee107e92a7db11f1f8c98a5c2867304f57ddc54'
HEAD = '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'
MODULE = 'TCSlib.Complexity.Randomized.PolyTimeModel'
REL = MODULE.replace('.', '/') + '.lean'
LABEL = 'G06Seal_004_TCSlib_Complexity_Randomized_PolyTimeModel'
OUT = Path('/private/tmp/gate06-polytimemodel-final-review')
RANGES = [
 ('polyTimeComputable_takePrefixByLen',124,126), ('polyTimeComputable_dropPrefixByLen',132,134),
 ('polyTimeComputable_sliceTake',141,159), ('polyTimeComputable_sliceDrop',164,182),
 ('polyTimeModel_closedUnderRace',193,221), ('polyTimeModel_closedUnderAnswerIs',227,250),
 ('polyTimeModel_closedUnderMajority',259,309), ('polyTimeModel_closedUnderAny',316,351),
 ('polyTimeModel_closedUnderNot',355,361), ('polyTimeModel_closedUnderShiftOr',373,401),
 ('polyTimeModel_verifierHasCircuits',418,480), ('inSigma2_polyTimeModel_iff',497,543),
 ('sipser_gacs_polyTime',561,568)]

def sha(raw): return hashlib.sha256(raw.encode() if isinstance(raw,str) else raw).hexdigest()
def read(p): return json.loads(p.read_bytes())
def git(*args): return subprocess.check_output(['git','--no-optional-locks','-C',str(ROOT),*args],stderr=subprocess.PIPE)
cache={}
def source(ref,path):
 if (ref,path) not in cache: cache[ref,path]=git('show',ref+':'+path)
 return cache[ref,path]
def insertions(path):
 b,h=source(BASE,path),source(HEAD,path);bl,hl=b.splitlines(keepends=True),h.splitlines(keepends=True)
 rows=[];recovered=[]
 for tag,a,z,c,d in difflib.SequenceMatcher(a=bl,b=hl,autojunk=False).get_opcodes():
  assert tag in {'equal','insert'},(path,tag)
  if tag=='equal': recovered+=hl[c:d]
  else:
   raw=b''.join(hl[c:d]);text=raw.decode()
   assert '@[' not in text and not re.search(r'(?m)^\s*(?:def|instance|structure|inductive|class|abbrev|opaque|axiom|attribute|open|namespace|end|variable|set_option|notation|macro|elab|syntax)\b',text)
   rows.append({'head_range':[c+1,d],'raw_sha256':sha(raw),'raw':text,
                'theorem_source_names':re.findall(r'(?m)^theorem\s+(\S+)',text)})
 assert b''.join(recovered)==b
 return {'base_sha256':sha(b),'head_sha256':sha(h),'base_lines':len(bl),'head_lines':len(hl),
         'only_insertions':True,'removing_insertions_reproduces_entire_base':True,'insertions':rows}

def main():
 pins=read(E/'pins.json');assert (pins['base'],pins['head'])==(BASE,HEAD)
 for ref in [BASE,HEAD]:assert git('rev-parse',ref+'^{commit}').decode().strip()==ref
 cp=E/'native-seal-runs'/(LABEL+'.classification.json');craw=cp.read_bytes();record=json.loads(craw)
 p=next(p for p in read(E/'seal-manifest.json')['probes'] if p['module']==MODULE)
 assert record['module']==MODULE and record['label']==LABEL and record['valid_harness'] is True
 assert record['head_before_and_after']==HEAD and record['source_failure'] is True
 assert record['result']['rc']==1 and record['result']['error_diagnostics']==16
 logp=Path(record['log']);lograw=logp.read_bytes();log=lograw.decode()
 assert sha(lograw)==record['log_sha256']
 rp=Path(record['result_path']);assert sha(rp.read_bytes())==record['result_json_sha256'] and read(rp)==record['result']
 probe=Path(p['probe_path']).read_bytes();assert probe==Path(p['saved_source']).read_bytes()
 assert sha(probe)==p['probe_sha256']==record['captured_probe_sha256']==record['result']['source_sha256']
 recovered=probe
 for row in reversed(p['insertions']):
  a,z=row['probe_byte_offset'],row['byte_count'];assert sha(recovered[a:a+z])==row['sha256']
  recovered=recovered[:a]+recovered[a+z:]
 assert recovered==source(HEAD,REL) and sha(recovered)==p['source_sha256']
 actual={}
 for m in re.finditer(r'(?m)^.*?G06-NAME label=(\S+) spelling=(.*?) actual=(.*?) home=(\S+) before=Lean\.ReducibilityStatus\.(\w+) installed=Lean\.ReducibilityStatus\.(\w+)\s*$',log):
  lab,spelling,name,home,before,installed=m.groups();assert lab==LABEL and spelling==name and installed=='irreducible' and spelling not in actual
  actual[spelling]=(home,before)
 assert actual=={r['spelling']:(r['home'],r['collector_reducibility']) for r in p['requested_names']}
 assert p['requested_count']==1568 and p['collector_active_candidate_count']==1550 and p['collector_irreducible_count']==18
 assert len(re.findall(r'G06-SEAL label='+LABEL+r' requested=1568 active=1550 already_irreducible=18 verified=1568\s*$',log,re.M))==1
 assert len(re.findall(r'G06-SEAL-END label='+LABEL+r' requested=1568 verified=1568\s*$',log,re.M))==1
 assert re.findall(r'(?m)^END (\S+) RC (-?\d+)\s*$',log)==[(record['result']['end'],'1')]
 errs=list(re.finditer(r'(?m)^([^\n]*?\.lean):(\d+):(\d+): error(?:\(([^\n)]*)\))?:([^\n]*)',log))
 assert len(errs)==len(record['errors'])==16
 inverse={r['probe_line']:r['source_line'] for r in p['source_to_probe_lines']}
 byname=defaultdict(list)
 hl=source(HEAD,REL).splitlines(keepends=True);bl=source(BASE,REL).splitlines(keepends=True)
 for m,e in zip(errs,record['errors']):
  assert (int(m[2]),int(m[3]),m[4] or None,log.count('\n',0,m.start())+1)==(e['probe_line'],e['probe_column'],e['error_code'],e['log_line'])
  assert (ROOT/e['path']).resolve()==Path(p['probe_path']).resolve()
  assert inverse[e['probe_line']]==e['source_line'] and hl[e['source_line']-1]==probe.splitlines(keepends=True)[e['probe_line']-1]
  byname[e['source_name']].append(e)
 history=[];history_pins={}
 for n in ['cleanup-b-decls.tsv','cleanup-b.tsv']:
  raw=(HIST/n).read_bytes();history_pins[n]=sha(raw)
  for i,l in enumerate(raw.decode().splitlines(),1):
   f=re.split(r'\t|\\t',l)
   if n=='cleanup-b-decls.tsv' and len(f)>=2:path,name=f[:2]
   elif n=='cleanup-b.tsv' and len(f)>=4:path,name=f[2],re.sub(r'^(?:theorem|lemma|def|instance|structure|inductive|abbrev|class)\s+','',f[3])
   else:continue
   history.append({'inventory':n,'line':i,'file':path,'name':name})
 rows=[]
 for name,a,z in RANGES:
  raw=b''.join(hl[a-1:z]);oldraw=b''.join(bl[a-10:z-9]);assert raw==oldraw
  assert hl[a-1].decode().startswith('theorem '+name) and not hl[z].strip()
  after=next(l.decode().strip() for l in hl[z:] if l.strip());assert after.startswith(('/--','end '))
  es=byname[name];assert all(a<=e['source_line']<=z and e['declaration_start']==a and e['qualified_source_name']=='Randomized.'+name for e in es)
  variants={name,'Randomized.'+name}
  exact=[r for r in history if r['file']==REL and r['name'] in variants]
  same_elsewhere=[r for r in history if r['file']!=REL and r['name'] in variants]
  rows.append({'module':MODULE,'file':REL,'name':name,'full_source_name':'Randomized.'+name,
   'base_range':[a-9,z-9],'head_range':[a,z],'raw_header_body_sha256':sha(raw),'raw_header_body':raw.decode(),
   'raw_header_body_identical':True,'diagnostics':len(es),'errors':es,'historical_exact_rows':exact,
   'historical_same_name_other_files':same_elsewhere,'inventory_key_status':'NO_EXACT_KEY_IN_FROZEN_764_INVENTORY' if not exact else 'EXACT_KEY_LINK',
   'source_observation_recommendation':'New inherited source-identity witness for root review; failure retained',
   'failure_retained':True,'waiver':False,'source_base_native_seal_replay':False})
 assert set(byname)=={r[0] for r in RANGES} and len(rows)==13 and sum(r['diagnostics'] for r in rows)==16
 closure=read(E/'closures.json')[MODULE];assert len(closure)==81
 context=[];changed=[]
 for m in closure:
  path=m.replace('.','/')+'.lean';b,h=source(BASE,path),source(HEAD,path)
  context.append({'module':m,'file':path,'base_sha256':sha(b),'head_sha256':sha(h),'raw_identical':b==h})
  if b!=h:changed.append(path)
 assert set(changed)=={'TCSlib/Complexity/Randomized/Classes.lean','TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean'}
 insert_reports={path:insertions(path) for path in [REL,*changed]}
 assert [r['theorem_source_names'] for r in insert_reports[REL]['insertions']]==[['polyTimeModel_eff_iff']]
 assert len(insert_reports[changed[0]]['insertions']) in {3,4}
 assert b''.join(hl[:83]+hl[92:])==source(BASE,REL)
 added_names={name for report in insert_reports.values() for row in report['insertions'] for name in row['theorem_source_names']}
 assert all(not re.search(r"(?<![\w'])"+re.escape(name)+r"(?![\w'])",row['raw_header_body']) for name in added_names for row in rows)
 configs={}
 for path in ['lean-toolchain','lake-manifest.json']:
  b,h=source(BASE,path),source(HEAD,path);assert b==h;configs[path]={'base_sha256':sha(b),'head_sha256':sha(h),'raw_identical':True}
 initialp=ROOT/'.lake/ps-maintainer/gate06/repairs/inherited-full-survey-review.json';initial=read(initialp)
 assert not any(r['file']==REL for k in ['declarations','linked_prior_declarations'] for r in initial[k])
 operative=[]
 suffixes=['PrefixByLength.take','PrefixByLength.drop','PolyTimeComputable','polyLen','ClosedUnderRace','ClosedUnderAnswerIs','ClosedUnderMajority','ClosedUnderAny','ClosedUnderNot','ClosedUnderShiftOr','VerifierHasCircuits','InPPoly','InSigma2','InPi2']
 for s in suffixes:
  for r in p['requested_names']:
   if r['spelling']==s or r['spelling'].endswith('.'+s): operative.append(r)
 report={'schema':'gate06-polytimemodel-final-static-witness/v1','status':'ALL_16_SOURCE_DIAGNOSTICS_RETAINED_ROOT_REVIEW_REQUIRED',
  'base':BASE,'head':HEAD,'module':MODULE,'source':REL,'classification_file':str(cp),'classification_sha256':sha(craw),
  'reproducer_sha256':sha(Path(__file__).read_bytes()),
  'native_log':str(logp),'native_log_sha256':sha(lograw),'native_result_sha256':record['result_json_sha256'],
  'base_file_sha256':sha(source(BASE,REL)),'head_file_sha256':sha(source(HEAD,REL)),
  'probe_sha256':p['probe_sha256'],'probe_recovers_exact_head_source':True,
  'native_seal_checks':{'requested':1568,'active':1550,'already_irreducible':18,'exact_actual_name_home_status_rows_verified':len(actual),'install_and_EOF_present':True},
  'counts':{'failing_declarations':13,'source_diagnostics':16,'new_or_changed_failing_header_body_blocks':0,
            'exact_historical_inventory_keys':sum(bool(r['historical_exact_rows']) for r in rows),
            'new_observation_keys_for_root_review':sum(not r['historical_exact_rows'] for r in rows),
            'diagnostics_on_new_polyTimeModel_eff_iff':0},
  'declarations':rows,'same_file_and_changed_imports_insertions':insert_reports,
  'namespace_binding_context':{'same_namespace':'Randomized','same_open':'Complexity','direct_imports_options_module_prose_and_binding_commands_unchanged':True,
    'all_preexisting_declarations_docs_and_bodies_in_changed_context_files_unchanged':True,
    'insertions_are_plain_theorems_without_simp_or_instance_attributes':True,
    'new_reader_names_are_not_referenced_by_failing_proofs':True,
    'interpretation':'Source contracts and operative definitions are unchanged; only unused public reading equations were added.'},
  'import_closure':context,'operative_foreign_definition_rows':operative,'compiler_source_configuration':configs,
  'historical_inventory_sha256':history_pins,'initial_review_sha256':sha(initialp.read_bytes()),'initial_review_covers_this_module':False,
  'limits':['Static Git/source witness only; no independently executed native check or base-source seal replay.',
            'This is an inherited source-observation recommendation, never a pass/exclusion/waiver.',
            'Root must review and record new observation keys with exact hashes and historical dedup results.',
            'Other final modules and the complete 54-module reconciliation are outside this module review.']}
 (OUT/'PolyTimeModel-final-failure-review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'counts':report['counts'],'changed_context_files':changed,'historical_cross_file_same_name_hits':sum(len(r['historical_same_name_other_files']) for r in rows),
  'json_sha256':sha((OUT/'PolyTimeModel-final-failure-review.json').read_bytes())},indent=2))

if __name__ == '__main__':
 main()
