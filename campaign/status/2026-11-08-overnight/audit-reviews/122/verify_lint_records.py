from pathlib import Path
import json,re,collections,hashlib,subprocess
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/gates/122-first-halt-reuse/review/inputs/current77/qa';H=lambda b:hashlib.sha256(b).hexdigest();g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);rec='6fd9cd541adb15af0d4f18fb35c4eb77ac02f7fd';runs=json.loads((P/'RUNS.json').read_text());owners=sorted({r['owner'] for r in json.loads((O/'SOURCE-VERIFICATION.json').read_text())['roots']});result={}
for kind,helper in [('style','style_lint.py'),('campaign','campaign_style_lint.py')]:
 raw=(P/'helpers'/helper).read_bytes();assert raw==g('show',rec+':scripts/'+helper);groups={};counts={}
 for side in ['BASE','HEAD']:
  d=json.loads((P/(side+'-'+kind+'-findings.json')).read_text());assert sorted(d['explicit_files'])==owners and d['count_files']==8;assert d['exit']==(1 if kind=='style' else 0)
  if kind=='campaign':assert d['default_CHECK8B'] is False
  r=next(r for r in runs if r['side']==side and r['kind']==kind);assert r['helper_sha256']==H(raw) and r['adapter_sha256']==H((P/'lint_adapter.py').read_bytes());group=collections.Counter()
  for row in d['findings']:
   msg=row['message'];path=row['path']
   if kind=='style':
    m=re.match(re.escape(path)+r'(?::\d+)?: (.*)',msg);assert m;msg=m.group(1)
   else:msg=re.sub(r'^line \d+: ','',msg)
   msg=re.sub(r'^\d+ lines (?=>|\(>)','<N> lines ',msg);msg=re.sub(r'proof is \d+ lines','proof is <N> lines',msg);msg=re.sub(r'^\d+ lines;','<N> lines;',msg);group[(path,row.get('level','FINDING'),msg)]+=1
  groups[side]=group;counts[side]={'total':len(d['findings']),'levels':dict(collections.Counter(x.get('level','FINDING') for x in d['findings']))}
 assert groups['BASE']==groups['HEAD'];result[kind]={'canonical_helper_sha256':H(raw),'adapter_sha256':H((P/'lint_adapter.py').read_bytes()),'endpoint_counts':counts,'new_or_removed_normalized_identity_occurrences':0,'normalization':'source line positions and dynamic line/proof counts only; semantic text/names/severity preserved','independent_linter_execution':False}
result['limits']='Pure parsing/hash/identity comparison of stored actual lint receipts; no new lint or source execution.';(O/'LINT-RECORD-VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
