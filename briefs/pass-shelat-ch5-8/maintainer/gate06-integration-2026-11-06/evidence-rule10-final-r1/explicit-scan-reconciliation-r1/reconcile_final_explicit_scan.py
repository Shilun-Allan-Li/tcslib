"""Reconcile fresh C1/C2/C3 against the exhaustive source review; no Lean or source edits."""
from pathlib import Path
import csv,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
ROOT=Path.cwd(); R=ROOT/'.lake/ps-maintainer/gate06/repairs'
E=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1')
BASE='eee107e92a7db11f1f8c98a5c2867304f57ddc54';HEAD='3f6db40e1688c4a0bb922c9575dd3bd2157a650b'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def need(ok,message):
 if not ok:raise RuntimeError(message)

def load(path,digest,name):
 need(sha(path)==digest,'reviewed parser wrapper changed')
 spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def main():
 out=R/'final-explicit-scan-reconciliation-r1';need(not out.exists(),'do not overwrite a reconciliation')
 helper=load(R/'reconcile_gate06_final_failures.py','cd999cae32990e1ddf721a60e51a668613c139fc9892df883253912e6d90a6cd','g06_scan_parser_loader')
 parser=helper.load_parser()
 need(subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==HEAD,'wrong HEAD')
 summary=json.loads((R/'final-explicit-classification.json').read_text())
 need(summary['head']==HEAD and summary['base']==BASE and summary['new_or_touched_foreign_definition_items']==summary['unresolved_new_or_touched_items']==0,'source classification does not clear the delta')
 inherited=list(csv.DictReader((R/'final-explicit-inherited-debt.tsv').open(),delimiter='\t'))
 static={(x['path'],int(x['head_line']),x['foreign_name']):x for x in inherited}
 need(len(static)==len(inherited)==134,'unexpected static inherited inventory')
 sections={};current=None
 for line in (R/'final-explicit-scan-r1/scan.log').read_text().splitlines():
  if line.startswith('## '):current=line;sections[current]=[]
  elif current and line and not line.startswith('#'):sections[current].append(line.split('\t'))
 c1,c2,c3=[v for k,v in sections.items()]
 need((len(c1),len(c2),len(c3))==(142,10,3),'fresh scan totals differ')
 source_cache={};parsed={}
 def source(ref,path):
  if (ref,path) not in source_cache:source_cache[ref,path]=subprocess.check_output(['git','show',ref+':'+path],text=True)
  return source_cache[ref,path]
 def decls(ref,path):
  if (ref,path) not in parsed:parsed[ref,path]=parser.parse(source(ref,path))
  return parsed[ref,path]
 def block(path,line):
  found=[d for d in decls(HEAD,path) if d['start']<=line<=d['end']];need(len(found)==1,'ambiguous source location')
  h=found[0];old=[d for d in decls(BASE,path) if d['canonical']==h['canonical'] and d['kind']==h['kind']];need(len(old)==1,'ambiguous base block')
  b=old[0];need(h['raw']==b['raw'] and h['scope_stack']==b['scope_stack'] and h['context_commands']==b['context_commands'],'new/changed explicit-read or show/change block')
  return {'file':path,'canonical':h['canonical'],'head_range':[h['start'],h['end']],'base_range':[b['start'],b['end']],'raw_block_sha256':hashlib.sha256(h['raw'].encode()).hexdigest(),'complete_raw_header_body_equal':True}
 matched=[];core=[];seen=set()
 for f in c1:
  path,line=f[0].rsplit(':',1);key=(path,int(line),f[4])
  if f[5].startswith('TCSlib'):
   need(key in static,'raw TCSlib hit not in exhaustive inherited source inventory');seen.add(key);matched.append({'raw':f,'inherited_record':static[key]})
  else:core.append({'raw':f,**block(path,int(line)),'classification':'RETAINED_INHERITED_NON_TCS_EXPLICIT_READ'})
 need(len(matched)==124 and len(core)==18,'unexpected kind split')
 supplement=[static[k] for k in sorted(set(static)-seen)]
 need(len(supplement)==10 and all(x['path']=='TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean' and x['foreign_name']=='TCSlib.Cryptography.PrivateKeyScheme.encodeList' for x in supplement),'unexpected textual resolution omission')
 need('open PrivateKeyScheme (encodeList)' in source(HEAD,supplement[0]['path']) and 'open PrivateKeyScheme (encodeList)' in source(BASE,supplement[0]['path']),'selected-open witness absent')
 kinds={}
 for line in (R/'final-explicit-native-table-r1/native-kinds.tsv').read_text().splitlines():
  n,k,m=line.split('\t');kinds[n]=(k,m)
 for x in inherited:
  expected_home=x['foreign_home'][:-5].replace('/','.')
  need(x['foreign_name'] in kinds and kinds[x['foreign_name']][0].startswith('def') and kinds[x['foreign_name']][1]==expected_home,'inherited source kind/home disagrees with actual native metadata')
 failures=json.loads((E/'failure-disposition-r1/disposition.json').read_text());failure_keys={(x['file'],x['canonical']) for x in failures['declarations']}
 shows=[]
 for f in c2:
  path,line=f[0].rsplit(':',1);d=block(path,int(line));need((path,d['canonical']) in failure_keys,'show/change not in retained final failures');shows.append({'raw':f,**d})
 refs=json.loads((R/'final-c3-extracted-r2/all-refs.json').read_text())
 need({tuple(x) for x in c3}=={(x['module'],x['owner'],x['parent'],x['reference']) for x in refs},'scanner C3 differs from complete fresh extraction')
 mods=json.loads((E/'modules.json').read_text());anonymous=[]
 lexer=load(ROOT/'.lake/ps-maintainer/gate06/build_seals.py','fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a','g06_scan_lexer')
 for module,path in mods.items():
  code=lexer.header(source(HEAD,path).encode())['code']
  for m in re.finditer(r'(?<![\w.])(?:example|run_cmd|run_elab)\b|#(?:eval|check|reduce)\b',code):anonymous.append({'file':path,'line':code[:m.start()].count('\n')+1,'token':m.group()})
 need(not anonymous,'anonymous/metaprogram source requires separate term/reference review')
 data={'base':BASE,'head':HEAD,'status':'FRESH_SOURCE_SCAN_RECONCILED_NO_MERGE_CLEARANCE','raw_scan':{'c1':142,'c2':10,'c3':3,'all_54_files':True,'all_138_source_errors_supplied':True,'all_54_c3_files_supplied':True},'c1_raw_tcs_matches':124,'c1_raw_non_tcs_inherited':18,'c1_selected_open_supplement':10,'inherited_tcs_candidates':134,'inherited_tcs_debt':131,'exact_PolyExpr_eval_exceptions_retained':3,'new_or_touched_explicit_read_items':0,'unresolved_new_or_touched_items':0,'new_or_touched_item_count':1555,'complete_explicit_item_count':4119,'c2_all_retained_base_failures':True,'c3_all_three_pairs_retained':True,'anonymous_or_meta_commands_in_54_sources':anonymous,'matched_tcs':matched,'non_tcs_inherited':core,'selected_open_supplement':supplement,'shows_at_retained_failures':shows,'c3_raw_rows':c3,'input_sha256':{str(p):sha(p) for p in [Path(__file__),R/'final-explicit-scan-r1/scan.log',R/'final-explicit-classification.json',R/'final-explicit-inherited-debt.tsv',R/'final-c3-extracted-r2/summary.json',E/'failure-disposition-r1/disposition.json']},'limits':['The legacy text resolver misses the selected open PrivateKeyScheme(encodeList); ten exhaustive-source observations are retained as a supplement.','Raw counts mix observations and source/declaration units and must not be summed into the764 inventory.','Inherited source reads and failed seals remain debt, not passes or exclusions.','C3 source/context disposition is separate; extraction alone is not clearance.']}
 need(subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==HEAD,'HEAD changed')
 out.mkdir();(out/'reconciliation.json').write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({k:v for k,v in data.items() if k in ['status','raw_scan','c1_raw_tcs_matches','c1_raw_non_tcs_inherited','c1_selected_open_supplement','new_or_touched_explicit_read_items','unresolved_new_or_touched_items']}))

if __name__=='__main__':main()
