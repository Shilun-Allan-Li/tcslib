#!/usr/bin/env python3
"""Own read-only consumer for the FUTURE completed59 survey; never invokes Lean/Git.

Writes only a new output directory. All current diagnostics remain failures;
source/operational comparisons and historical links never grant a waiver.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_context',HERE/'source_context.py');sc=importlib.util.module_from_spec(sp);sp.loader.exec_module(sc)
ROOT=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
HEAD='a495f3953afff46ad5dec2d29ac8a7f55bd8ae37';BASE='067c5d8d6dd436e62681d7dc607984c705dc80a2'
ERROR=re.compile(r'(?m)^([^\n]*?\.lean):(\d+):(\d+): error(?:\(([^\n)]*)\))?:([^\n]*)')

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):
 def unique(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(p.read_bytes(),object_pairs_hook=unique)
def encode(x):return (json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode()
def root_records(log):
 result={};allkeys=set()
 for line in log.splitlines():
  mt=re.search(r'\bG06-ROOT (\{.*\})$',line)
  if not mt:continue
  r=json.loads(mt[1]);m=r['module']['display'];key=sc.actual_key(r['name']);need(key not in allkeys,'duplicate actual root component identity');allkeys.add(key);result.setdefault(m,[]).append(r)
 return result

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--evidence',type=Path,required=True);ap.add_argument('--preflight',type=Path,default=HERE/'preflight');ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 pf=args.preflight.resolve();out=args.output.resolve();need(out.is_relative_to(HERE.resolve()) and not out.exists(),'NEW ignored output required')
 pm=j(pf/'preflight-manifest.json');need(pm['head']==HEAD and pm['actual_PRbase']==BASE,'wrong preflight pins')
 for n,h in pm['files'].items():need(sha((pf/n).read_bytes())==h,'preflight changed: '+n)
 need(sha((HERE/'source_context.py').read_bytes())==pm['source_parser_sha256'],'source parser changed')
 idx=j(pf/'all59-source-envelope-indices.json');snaps=j(pf/'source-snapshots.json');closures=j(pf/'context-closures.json');contexts=j(pf/'operative-context-comparisons.json');prior=j(pf/'prior-witnesses.json');history=j(pf/'historical-ledger-index.json')['rows']
 need(all(v['head'].get('parser_version')=='R2_ATTRIBUTE_AWARE_FAIL_CLOSED' and
   (v['actual_PRbase'].get('parser_version')=='R2_ATTRIBUTE_AWARE_FAIL_CLOSED' or
    (v['actual_PRbase'].get('missing_source') is True and v['actual_PRbase'].get('units')==[])) for v in idx.values()),'not rebuilt R2 source indices or explicit absent-base source')
 e=args.evidence.resolve();summary=j(e/'native-seal-runs/summary.json');cfg=j(e/'native-seal-runs/configuration.json');pins=j(e/'pins.json');mods=j(e/'modules.json');manifest=j(e/'seal-manifest.json')
 need(summary['head']==pins['head']==cfg['head']==HEAD and pins['actual_campaign_base']==BASE,'not the current combined native epoch')
 need(summary['complete'] and summary['aborted_reason'] is None and summary['completed_probes']==summary['expected_probes']==len(summary['results'])==len(mods)==59,'not complete59')
 need(set(mods)==set(idx)==set(contexts),'scope/context comparisons differ from frozen59')
 need(all(idx[m]['actual_PRbase'].get('missing_source',False)==(path not in snaps[BASE]['sources']) for m,path in mods.items()),'absent-base index disagrees with exact base source inventory')
 need(sha((e/'native-seal-runs/configuration.json').read_bytes())==summary['configuration_sha256'],'configuration hash differs')
 expected_runner='0a8b5ebc13d5b2cd4f613fbecb83a357daad285ef84e29774180378f3430a52b'
 need(sha((e/'native-seal-runs/driver.source.txt').read_bytes())==cfg['driver_sha256']==expected_runner,'not the reviewed combined runner')
 probes={p['module']:p for p in manifest['probes']};need(len(probes)==len(manifest['probes'])==59 and set(probes)==set(mods),'seal manifest scope incomplete')
 need({r['module'] for r in summary['results']}==set(mods),'native result module scope incomplete')
 # Exact full registry is attached per owner, including every private/generated/opaque root.
 roots=root_records((e/'collect1.log').read_text());need(set(roots)==set(mods),'fresh ROOT registry missing modules')
 out.mkdir();blobs={};captures=[]
 def put(raw):
  h=sha(raw);p=out/'blobs'/h
  if h not in blobs:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw);blobs[h]={'path':'blobs/'+h,'bytes':len(raw)}
  return h
 def capture(p,h=None):
  need(p.is_file() and not p.is_symlink(),'nonordinary captured file');raw=p.read_bytes();need(h is None or sha(raw)==h,'native capture digest differs');digest=put(raw);captures.append({'path':str(p),'sha256':digest});return raw
 capture(e/'native-seal-runs/summary.json');capture(e/'native-seal-runs/configuration.json');capture(e/'seal-manifest.json');capture(e/'collect1.log');capture(e/'pins.json');capture(e/'modules.json')
 rows=[];harness=[];total=0
 for record in summary['results']:
  m=record['module'];p=probes[m];path=mods[m];errors=record.get('errors',[]);total+=len(errors)
  if not errors and record.get('valid_harness'):continue
  if not record.get('valid_harness'):
   kept={'record':record,'errors':errors,'available_native_captures':[],'status':'HARNESS_OR_SETUP_FAILURE_NOT_SOURCE_EVIDENCE'}
   for field,digestfield in [('log','log_sha256'),('result_path','result_json_sha256')]:
    if record.get(field) and Path(record[field]).is_file():
     data=capture(Path(record[field]),record.get(digestfield));kept['available_native_captures'].append({'field':field,'sha256':sha(data)})
   harness.append(kept);continue
  native_log=Path(record['log']);native_result=Path(record['result_path']);lb=capture(native_log,record['log_sha256']);rb=capture(native_result,record['result_json_sha256']);need(j(native_result)==record['result'],'result embed mismatch')
  parsed=list(ERROR.finditer(lb.decode()));need(len(parsed)==len(errors)==record['result']['error_diagnostics'],'diagnostics dropped')
  pb=capture(native_log.with_name(record['label']+'.source.txt'),p['probe_sha256']);need(record['captured_probe_sha256']==p['probe_sha256'],'native probe identity differs')
  recovered=pb
  for addition in reversed(p['insertions']):
   at,n=addition['probe_byte_offset'],addition['byte_count'];need(sha(recovered[at:at+n])==addition['sha256'],'insertion bytes differ');recovered=recovered[:at]+recovered[at+n:]
  source_meta=snaps[HEAD]['sources'][path];source=(pf/'blobs'/source_meta['sha256']).read_bytes();need(recovered==source and sha(source)==p['source_sha256'],'source/probe restoration differs from exact a495')
  inverse={r['probe_line']:r['source_line'] for r in p['source_to_probe_lines']};headindex=idx[m]['head'];baseindex=idx[m]['actual_PRbase'];text=source.decode()
  module_roots=roots[m];module_root_blob=put(encode(module_roots))
  for n,(mt,error) in enumerate(zip(parsed,errors)):
   need(int(mt[2])==error['probe_line'] and int(mt[3])==error['probe_column'] and (mt[4] or None)==error['error_code'] and lb.decode().count('\n',0,mt.start())+1==error['log_line'],'raw diagnostic coordinates differ')
   line=inverse.get(error['probe_line']);need(line==error['source_line'],'source line map differs')
   units=sc.select_unit(headindex,line) if isinstance(line,int) else [];comparisons=[]
   for u in units:
    raw=text[u['char_start']:u['char_end']].encode();need(sha(raw)==u['raw_sha256'],'full source unit recovery differs');raw_blob=put(raw)
    safe=len(units)==1 and sc.mapping_safe(u)
    matches=sc.match_unit(baseindex,u) if safe else [];b=matches[0] if len(matches)==1 else None;base_raw=None
    if b:
     bt=(pf/'blobs'/snaps[BASE]['sources'][path]['sha256']).read_text();base_raw=bt[b['char_start']:b['char_end']].encode();need(sha(base_raw)==b['raw_sha256'],'base full unit recovery differs');put(base_raw)
    parts=[['str',p] for p in u['canonical_parts']] if safe else None
    correspondences=[{'native_name':r['name'],'basis':'LEXICAL_SOURCE_COMPONENT_CORRESPONDENCE_NOT_ELABORATED_IDENTITY',
      'private_wrapper_removed_in_source_view':r['name']['components']!=sc.user_parts(r['name']['components'])}
      for r in module_roots if parts is not None and sc.user_parts(r['name']['components'])==parts]
    family=[r['name'] for r in module_roots if parts is not None and len(sc.user_parts(r['name']['components']))>len(parts) and sc.user_parts(r['name']['components'])[:len(parts)]==parts]
    canonical=u['canonical'] if safe else None;short=u['source_name'] if safe else None
    unique=short and sum(q['source_name']==short for q in headindex['units'])==1 and sum(q['source_name']==short for q in baseindex['units'])<=1
    links=[r for r in history if safe and r['file']==path and sc.source_key_matches(u,r['normalized_source_key'])]
    spelling_candidates=[r for r in history if safe and r['file']==path and unique and r['normalized_source_key']==short.removeprefix('_root_.') and not sc.source_key_matches(u,r['normalized_source_key'])]
    historical_correspondences=[i for i,r in enumerate(prior['historical_roots']) if safe and r['file']==path and sc.source_key_matches(u,r['historical_source_key'])]
    comparisons.append({'head':u,'head_raw_blob':raw_blob,'actual_PRbase':b,'base_match_count':len(matches),'base_raw_blob':sha(base_raw) if base_raw else None,
       'source_mapping_status':'UNIQUE_LEXICAL_SOURCE_ENVELOPE_NOT_ACTUAL_NAME' if safe else 'UNRESOLVED_LEXICAL_MAPPING_NO_FALLBACK',
       'header_code_equal':b['header_code_sha256']==u['header_code_sha256'] if b else None,'body_code_equal':b['body_code_sha256']==u['body_code_sha256'] if b else None,
       'namespace_scope_equal':b['namespace_parts']==u['namespace_parts'] and b['scope_stack']==u['scope_stack'] if b else None,
       'binding_trace_equal':b['binding_trace_sha256']==u['binding_trace_sha256'] if b else None,'complete_preceding_code_equal':b['complete_prefix_code_sha256']==u['complete_prefix_code_sha256'] if b else None,
       'prior115_source_correspondences':historical_correspondences,'exact_source_inventory_links':links,
       'source_spelling_inventory_candidates_not_identity_or_closure':spelling_candidates,
       'source_component_correspondences_not_identity_proofs':correspondences,'component_family_candidates_not_identity_proofs':family,
       'native_identity_limit':'Diagnostic qualified_source_name is annotation only. Exact source_line plus the R2 envelope determines lexical source mapping; all full native components remain independent. Neither equality of spelling nor removal of a private wrapper proves elaborated identity.'})
   # Complete raw log retained; the following slice also keeps every diagnostic's goal continuation.
   finish=parsed[n+1].start() if n+1<len(parsed) else len(lb.decode());chunk=lb.decode()[mt.start():finish].encode()
   rows.append({'module':m,'file':path,'diagnostic':error,'raw_diagnostic_blob':put(chunk),'raw_log_blob':sha(lb),'native_result_blob':sha(rb),'unit_candidates':comparisons,
      'source_mapping_status':'UNIQUE_LEXICAL_SOURCE_ENVELOPE_NOT_ACTUAL_NAME' if len(units)==1 and sc.mapping_safe(units[0]) else 'UNRESOLVED_LEXICAL_MAPPING_NO_NEXT_DECLARATION_FALLBACK',
      'source_blob':source_meta['sha256'],'actual_PRbase_source':snaps[BASE]['sources'].get(path),'complete_current_native_owner_registry_blob':module_root_blob,
      'operative_context_key':m,'operative_context_comparison':contexts.get(m),'complete_current_closure':closures[HEAD][m],'complete_actual_base_closure':closures[BASE][m],
      'status':'CURRENT_FAILURE_RETAINED_REVIEW_REQUIRED','waiver':False,'native_base_environment_rebuilt':False})
 need(len(rows)+sum(len(r['errors']) for r in harness)==total,'a current diagnostic was dropped or duplicated')
 need(len(rows)==summary['source_error_diagnostics'] and len(harness)==summary['harness_failures'],'summary diagnostic/harness totals differ')
 report={'status':'ALL_CURRENT_FAILURES_RETAINED_NO_WAIVER_R2_ATTRIBUTE_AWARE','head':HEAD,'actual_PRbase':BASE,'source_diagnostics':len(rows),'harness_records':harness,'diagnostics':rows,
  'complete_native_root_counts':{m:len(rs) for m,rs in roots.items()},'captures':captures,'blobs':blobs,
  'limits':['Raw equality is never inheritance acceptance; changed/new/touched/unknown context stays review-required.','Context is the COMPLETE transitive import-source superset, not a guessed semantic operation graph.','Native all-stored owner registry keeps every additional/generated/private actual Name; unresolved source mapping remains explicit.','Current native source/object/direct-prerequisite provenance and component-collector validation must be reviewed separately.','No historical pass/failed label transfers automatically into this new instance-inclusive epoch.']}
 (out/'current-failure-witnesses.json').write_bytes(encode(report));(out/'helper.source.txt').write_bytes(Path(__file__).read_bytes());print(json.dumps({'source_diagnostics_retained':len(rows),'harness_failures_retained':len(harness),'all_current_outcomes_remain_review_required':True}))

if __name__=='__main__':main()
