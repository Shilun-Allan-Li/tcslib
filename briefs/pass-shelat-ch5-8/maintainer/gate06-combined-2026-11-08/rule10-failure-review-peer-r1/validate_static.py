"""Own data/AST/Git-read-only validator; never imports reviewed helpers."""
from pathlib import Path
from collections import Counter
import ast
import hashlib
import json
import subprocess

W=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
A=W/'.lake/ps-maintainer/gate06-combined-20261108'
P=A/'rule10-failure-review-prep-r1'
OUT=A/'rule10-failure-review-peer-r1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def need(t,m):
 if not t:raise AssertionError(m)
def main():
 need(sha(P/'FINAL-MANIFEST.json')=='7a3a7dfc28bf29310271310da1541b1fdf20860d04968d5dd7a296c983030d42','frozen R1 manifest')
 m=load(P/'FINAL-MANIFEST.json')
 for n,r in m['files'].items():
  f=P/n;need(f.stat().st_size==r['bytes'] and sha(f)==r['sha256'],'frozen R1 leaf')
 for n in ['attach_current_failures.py','source_context.py','failure_preflight.py']:ast.parse((P/n).read_text())
 F=P/'preflight';pm=load(F/'preflight-manifest.json')
 for n,h in pm['files'].items():need(sha(F/n)==h,'preflight JSON leaf')
 bi=load(F/'blob-index.json')
 for h,r in bi.items():
  f=F/r['path'];need(f.stat().st_size==r['bytes'] and sha(f)==h,'content-addressed blob')
 ranges=load(P/'legacy-recorded-raw-range-validation.json')['rows'];cache={}
 for r in ranges:
  key=(r['ref'],r['file'])
  if key not in cache:cache[key]=subprocess.check_output(['git','--no-optional-locks','show',r['ref']+':'+r['file']],cwd=W)
  lo,hi=r['range'];raw=b''.join(cache[key].splitlines(keepends=True)[lo-1:hi]);need(hashlib.sha256(raw).hexdigest()==r['raw_sha256'],'original raw range vs exact Git')
 need(len(ranges)==230,'230 raw ranges')
 prior=load(F/'prior-witnesses.json')['historical_roots'];bad=[]
 for r in prior:
  comp=r['current_source_comparison'];u=comp['head']['unit'] if comp and comp.get('head') else None
  if u and r['historical_source_key'].removeprefix('_root_.')!=u['canonical']:
   bad.append({'file':r['file'],'historical_source_key':r['historical_source_key'],'incorrect_mapped_canonical':u['canonical'],'incorrect_current_envelope':[u['start_line'],u['end_line']],'incorrect_current_decl_line':u['declaration_line'],'observations':[{'source_line':o['diagnostic']['source_line'],'ref':o['ref'],'envelopes':[{'canonical':b['unit']['canonical'],'range':[b['unit']['start_line'],b['unit']['end_line']]} for b in o['source_envelope_candidates']]} for o in r['observations']]})
 need(len(prior)==115 and len(bad)==3,'three exact documented mapping defects')
 need({x['historical_source_key'] for x in bad}=={'Complexity.BinArith.uHead_nil','Complexity.BinArith.uRest_nil','TCSlib.Cryptography.Candidates.primesPairEquiv_apply_val'},'exact three keys')
 c=load(F/'operative-context-comparisons.json');need(len(c)==59,'59 contexts')
 historical_mods={r['module'] for r in prior};need(len(historical_mods)==21 and all(c[k]['complete_import_source_context_equal'] is False for k in historical_mods),'21 broad contexts remain different')
 data={'status':'R1_STATIC_REVIEW_BLOCKER_CONFIRMED_NO_HELPER_EXECUTION','reviewed_manifest_sha256':sha(P/'FINAL-MANIFEST.json'),'preflight_manifest_sha256':sha(F/'preflight-manifest.json'),'primary_helpers':{n:sha(P/n) for n in ['attach_current_failures.py','source_context.py','failure_preflight.py']},'verified_content_addressed_blobs':len(bi),'raw_ranges_verified_independently_against_Git':len(ranges),'raw_range_roles':dict(Counter((r['epoch']+':'+r['role']) for r in ranges)),'historical_root_keys':len(prior),'invalid_exact_source_mapping_count':len(bad),'invalid_exact_source_mappings':bad,'context_modules':len(c),'historical_failing_owner_modules':len(historical_mods),'all_historical_failing_complete_contexts_differ':True,'no_helper_import_or_execution':True,'no_native_or_current_failure_prediction':True,'limits':['Raw-range byte verification is distinct from declaration identity/correct envelope.','All115 current inheritance/equality interpretations remain review-required; three named envelope identities are invalid in R1.','Remaining mappings are not attested as actual generated/private Lean Names by this lexical review.']}
 with (OUT/'validation.json').open('x') as f:json.dump(data,f,indent=2);f.write('\n')
 print(json.dumps({'status':data['status'],'validation_sha256':sha(OUT/'validation.json'),'raw_ranges':len(ranges),'mapping_defects':len(bad)}))
if __name__=='__main__':main()
