"""Own independent data/AST/Git-read-only check; no reviewed helper imports."""
from pathlib import Path
from collections import Counter
import ast,hashlib,json,subprocess

W=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4');A=W/'.lake/ps-maintainer/gate06-combined-20261108'
P=A/'rule10-failure-review-prep-r2';F=P/'preflight';OLD=A/'rule10-failure-review-prep-r1';OUT=A/'rule10-failure-review-peer-r2'
PINS={'source_context.py':'d74ed2335ab68b9d8f96957c4e64f09371afd88c7e4163abb094e38ae44ee6b7','failure_preflight.py':'c745866fee37ffbfabb82659ab60fc76c64c2431364dc65d75c8a7650b7c7a1b','attach_current_failures.py':'ae3f0da57520670c08cdc43003c7989860df7653f08dbd4dc40616b1282410d6'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def h(raw):return hashlib.sha256(raw).hexdigest()
def load(p):return json.loads(p.read_text())
def need(t,m):
 if not t:raise AssertionError(m)
def safe(u):return u.get('canonical_parts') is not None and not u.get('lexical_boundaries_need_review') and not u.get('namespace_context_ambiguous')
def rowkey(r):return tuple(r[k] for k in ['inventory','line','file','normalized_source_key'])
def main():
 need(sha(P/'FINAL-MANIFEST.json')=='64fcc19bcec224831dfc02368f57e6f53a16f8e0eda3155cbfafb2ba9c443dbb','final outer pin')
 outer=load(P/'FINAL-MANIFEST.json');files=outer['files']
 need(len(files)==len({r['path'] for r in files})==4113,'exact outer unique file count')
 need({p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file()}=={r['path'] for r in files}|{'FINAL-MANIFEST.json'},'exact complete file set')
 for r in files:
  p=P/r['path'];need(p.resolve(strict=True).is_relative_to(P) and not p.is_symlink() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'outer leaf bytes')
 for n,s in PINS.items():need(sha(P/n)==s,'code pin');ast.parse((P/n).read_text())
 pm=load(F/'preflight-manifest.json');need(sha(F/'preflight-manifest.json')=='c5dd060a34db414fad7b163607487bf0c58d7d39e55a85c1d5f336cbf4a944db','preflight pin')
 for n,s in pm['files'].items():need(sha(F/n)==s,'preflight JSON hash')
 blobs=load(F/'blob-index.json')
 for digest,r in blobs.items():
  p=F/r['path'];need(p.stat().st_size==r['bytes'] and sha(p)==digest,'blob bytes')
 oldcheck=A/'rule10-failure-checkpoint-r1/FILES.json';oldfiles=load(oldcheck)['files']
 for r in oldfiles:
  p=OLD/r['path'];need(p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'R1 frozen bytes')
 need(sha(OLD/'FINAL-MANIFEST.json')=='7a3a7dfc28bf29310271310da1541b1fdf20860d04968d5dd7a296c983030d42','R1 manifest unchanged')
 old=load(OLD/'preflight/prior-witnesses.json')['historical_roots'];prior=load(F/'prior-witnesses.json')['historical_roots']
 key=lambda r:(r['historical_epoch'],r['file'],r['historical_source_key'])
 need(len(prior)==len({key(r) for r in prior})==115 and {key(r) for r in prior}=={key(r) for r in old},'all exact115 historical keys')
 need(sum(r['historical_head_diagnostics'] for r in prior)==145 and sum(r['historical_base_source_diagnostics'] for r in prior)==7,'all145+7 observations')
 oldby={key(r):r for r in old};resolved=[];unknown=[];exact=[];candidates=[]
 snapshots=load(F/'source-snapshots.json');head=pm['head'];base=pm['actual_PRbase']
 for r in prior:
  need(r['current_outcome']=='UNKNOWN_UNTIL_CURRENT59_NATIVE_SEALS' and r['failure_retained'] is True and r['waiver'] is False,'no waiver')
  oldobs=oldby[key(r)]['observations']
  need([{k:o[k] for k in ['raw_log_sha256','native_result_sha256','probe_sha256','diagnostic']} for o in r['observations']]==[{k:o[k] for k in ['raw_log_sha256','native_result_sha256','probe_sha256','diagnostic']} for o in oldobs],'raw observations retained')
  c=r['current_source_comparison']
  if c is None:unknown.append(r['historical_source_key']);continue
  u=c['head']['unit'];need(safe(u) and u['canonical']==r['historical_source_key'].removeprefix('_root_.'),'correct source key')
  for role,ref in [('head',head),('actual_base',base)]:
   b=c[role];v=b['unit'];text=(F/'blobs'/snapshots[ref]['sources'][r['file']]['sha256']).read_text();raw=text[v['char_start']:v['char_end']]
   need(h(raw.encode())==v['raw_sha256'],'exact unit bytes')
   at=v['declaration_keyword_char_start'];need(text[at:at+len(v['kind'])]==v['kind'] and text[at+len(v['kind']):].lstrip().startswith(v['source_name']),'keyword/name primary bytes')
  need(all(c[k] for k in ['raw_header_body_equal','header_code_equal','body_code_equal','namespace_scope_equal']),'114 safe source equality fields')
  resolved.append(r['historical_source_key']);exact.extend(r['exact_historical_inventory_links']);candidates.extend(r['historical_declared_spelling_candidates_not_canonical'])
  for e in r['exact_historical_inventory_links']:need(e['normalized_source_key'].removeprefix('_root_.').split('.')==u['canonical_parts'],'canonical only exact key')
  for e in r['historical_declared_spelling_candidates_not_canonical']:need(e['normalized_source_key']==u['source_name'].removeprefix('_root_.') and e['normalized_source_key']!='.'.join(u['canonical_parts']),'only spelling candidate')
 need(len(resolved)==114 and unknown==['TCSlib.Cryptography.GI.unaryMul_poly'],'114 safe plus1 explicit unresolved')
 oldunion=[e for r in load(P/'preparation-history/before-vertical-bar-and-link-guards/preflight/prior-witnesses.json')['historical_roots'] for e in r['exact_historical_inventory_links']]
 need(len(exact)==2 and len(candidates)==146 and Counter(map(rowkey,exact+candidates))==Counter(map(rowkey,oldunion)),'148 row union split2/146')
 idx=load(F/'all59-source-envelope-indices.json');contexts=load(F/'operative-context-comparisons.json');need(len(idx)==len(contexts)==59,'59 owners')
 missing=sum(v['actual_PRbase'].get('missing_source',False) for v in idx.values());need(missing==33 and all(v['head'].get('parser_version')=='R2_ATTRIBUTE_AWARE_FAIL_CLOSED' for v in idx.values()),'missing base only; all heads')
 unsafe=[(m,u['start_line'],u['mapping_warnings']) for m,x in idx.items() for u in x['head']['units'] if u['lexical_boundaries_need_review'] or u['namespace_context_ambiguous']]
 for c in contexts.values():
  for f in c['changed_context_files']:
   for side in ['left','right']:
    for u in f[side+'_definition_interface_inventory']:
     if u['header_body_boundary_status']=='UNRESOLVED':need(u['header_code_sha256'] is None and u['ordinary_body_code_sha256'] is None and u['unverified_lexical_split'] is not None,'unsafe split not authoritative')
 historical_modules={r['module'] for r in prior};need(len(historical_modules)==21 and all(contexts[m]['complete_import_source_context_equal'] is False for m in historical_modules),'all21 different conservative contexts')
 ranges=load(F/'legacy-recorded-raw-range-validation.json')['rows'];original=load(OLD/'legacy-recorded-raw-range-validation.json')['rows'];need([r['original_record'] for r in ranges]==original and len(ranges)==230,'exact230 original records')
 cache={}
 for r in ranges:
  d=r['original_record'];k=(d['ref'],d['file'])
  if k not in cache:cache[k]=subprocess.check_output(['git','--no-optional-locks','show',d['ref']+':'+d['file']],cwd=W)
  lo,hi=d['range'];need(h(b''.join(cache[k].splitlines(keepends=True)[lo-1:hi]))==d['raw_sha256']==r['exact_raw_blob'],'exact Git range bytes')
 report={'status':'INDEPENDENT_R2_AST_AND_IMMUTABLE_DATA_VALIDATION_PASS','outer_manifest_sha256':sha(P/'FINAL-MANIFEST.json'),'preflight_manifest_sha256':sha(F/'preflight-manifest.json'),'code_sha256':PINS,'outer_files_verified':len(files),'outer_file_bytes_verified':sum(r['bytes'] for r in files),'canonical_blobs_verified':len(blobs),'frozen_R1_files_verified':len(oldfiles),'R1_checkpoint_files_sha256':sha(oldcheck),'historical_keys':115,'historical_head_diagnostics':145,'historical_base_source_diagnostics':7,'safe_lexical_source_comparisons':len(resolved),'unresolved_historical_keys':unknown,'canonical_inventory_links':len(exact),'source_spelling_candidate_links':len(candidates),'exact148_union_preserved':True,'original230_ranges_verified_against_Git':len(ranges),'current_unsafe_envelope_count':len(unsafe),'current_unsafe_modules':len({m for m,_,_ in unsafe}),'absent_actual_base_owners':missing,'historical_changed_context_modules':len(historical_modules),'reviewed_helpers_imported_or_executed':False,'native_or_current_failure_prediction':False}
 with (OUT/'validation.json').open('x') as f:json.dump(report,f,indent=2);f.write('\n')
 print(json.dumps({'status':report['status'],'validation_sha256':sha(OUT/'validation.json'),'outer_files':len(files),'safe':len(resolved),'unknown':unknown,'canonical':len(exact),'candidates':len(candidates)}))
if __name__=='__main__':main()
