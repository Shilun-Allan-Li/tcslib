from pathlib import Path
import json,hashlib,datetime
root=Path(__file__).resolve().parents[1]
if (root/'MANIFEST.json').exists(): raise SystemExit('Frozen private packet; do not regenerate in place.')
def role(name):
 if name.startswith('evidence/actual-validation162/'):
  return 'Frozen162 actual selected metadata/guards/edges plus explicit original run/exclusion history. Exact original pins and theorem-boundary limits apply.'
 if name.startswith('evidence/source-QA119/current/'):
  return 'Current1096 source freeze/lints with actual argv/exits/raw/helpers; default-check8b false is explicit.'
 if name.startswith('evidence/source-QA119/historical63eb/'):
  return 'Historical63eb lint/source evidence, superseded for current findings.'
 if name.startswith('evidence/source-QA119/'):
  return 'Frozen119 source-QA metadata or reproduction script; current/historical split preserved.'
 if name.startswith('evidence/readiness149/') or name.startswith('evidence/prototype132/'):
  return 'Frozen prior preparation/authorization/conditional-route history; failed/debug/unexecuted statuses preserved, no extra current execution.'
 if name.startswith('source/'):
  return 'Complete selected BASE48/HEAD49 literal source with exact Git/package origin; no truncated capture.'
 if name.startswith('anchors/'):
  return 'Independent complete MAC8 text receipt/source/object-map anchor; binary snapshot not included.'
 if name.startswith('screen/historical-waitonly47-48/'):
  return 'Superseded47/48 request and terminated own idle waiter; no screen result or PASS.'
 if name.startswith('screen/shared-NAT-context/') or name=='screen/SHARED-RUN-NAT-INPUTS.json':
  return 'Unrelied-on NAT phase sources/raw and exact aliases needed for full shared-driver reproduction; no Ladner validation claim.'
 if name.startswith('screen/mapped-') or name=='screen/CAPTURE-MAPPING-SUMMARY.json':
  return 'Uncapped parser/source-coordinate index; every full literal source supplied. No pair-scoring execution by preparer.'
 if name.startswith('screen/actual-root-run/'):
  return 'Complete actual root shared-run request/driver/results/raw/pairdiff. Selected audit phases BASE48/LADNER49; NAT retained as shared context.'
 if name.startswith('screen/'):
  return 'Actual selected screen binding or independent linear all-pair comparison/dispositions; no new matching/Lean run.'
 if name.startswith('standards-current/'):
  return 'Full controls at final private observation recordscf5ada; no new approval inferred.'
 if name.startswith('standards/'):
  return 'Full initial captured standards/design/source check, original pin preserved; CURRENT-STANDARDS maps current authoritative captures.'
 if name.startswith('names/'):
  return 'Bounded available-ref name/shape query and complete line/source candidate dispositions; no global semantic absence.'
 if name.startswith('reproduction-tools/'):
  return 'Full sanitized helper/context reproduction input; actual execution identity limited by original receipts/bindings.'
 if name.startswith('bindings/'):
  return 'Source/package/relocation/identity or exact scope-boundary/preparation correction record. Dates/actor limits explicit.'
 if name.startswith('scripts/'):
  return 'Private text/hash/source preparation script, not source Lean, runtime instruction or extra comparison run.'
 return 'Private frozen draft narrative, exact population or inventory input. Final canonical publication/pins remain root-owned.'
excluded={'INPUT-INVENTORY.draft.json','BUNDLE-FILES.draft.txt','MANIFEST.json','SHA256SUMS.txt'}
rows=[]
for payload_file in sorted(root.rglob('*')):
 if payload_file.is_symlink():raise RuntimeError('Unexpected symlink '+str(payload_file))
 if not payload_file.is_file():continue
 name=str(payload_file.relative_to(root))
 if name in excluded:continue
 data=payload_file.read_bytes();data.decode('utf-8')
 rows.append({'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'role':role(name)})
(root/'INPUT-INVENTORY.draft.json').write_text(json.dumps({'status':'Preparation inventory; final MANIFEST is authoritative','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payloads_at_inventory':len(rows),'bytes_at_inventory':sum(row['bytes'] for row in rows),'excluded_recursive_inventory_and_freeze_files':sorted(excluded),'actual_comparison':'COMPLETE BASE48/LADNER49;2275 persistent/0 NEW/0 GONE/0 changed scores','remaining_root_publication':['Canonical R/X paths/pins and bundle counts/hash/prompt','Root review/adoption, Ready-to-dispatch status; user dispatch'],'files':rows},ensure_ascii=False,indent=2)+'\n')
(root/'BUNDLE-FILES.draft.txt').write_text('\n'.join(row['path'] for row in rows)+'\nINPUT-INVENTORY.draft.json\nMANIFEST.json\nSHA256SUMS.txt\n')
print(json.dumps({'inventory_payloads':len(rows),'inventory_bytes':sum(row['bytes'] for row in rows)}))
