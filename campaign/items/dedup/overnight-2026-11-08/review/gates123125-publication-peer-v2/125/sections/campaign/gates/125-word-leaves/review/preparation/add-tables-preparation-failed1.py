from pathlib import Path
import json,hashlib
O=Path('/private/tmp/ab34-small-gate-drafts');S=json.loads((O/'scope.json').read_text());Q=Path('/private/tmp/ab34-overnight-qa')
for item in S['items']:
 gate=item['gate'];d=O/str(gate);sf=item['source_freeze']['rows'][0];p=d/'pack-draft.md';s=p.read_text();mark='## Audited change\n';assert mark in s
 text='''## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
'''
 for side in ['BASE','HEAD']:
  text+='| '+side+' owner | `'+sf[side+'_blob']+'` Git blob; SHA256 `'+sf[side+'_sha256']+'` | `source/'+side+'/'+item['owner']+'.txt` |
 text+='| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `qa/source-freeze.json` and complete declfreeze stdout |\n'
 text+='| Selected metadata | '+str(len(item['roots']))+' roots; public/private role explicit; both sides must execute | `metadata/` full raw logs/requests and selected JSON |\n'
 text+='| Full screen population | Same33 source files at each side; no capped listing | `../screen-population.txt`, all complete files in `source/BASE` and `source/HEAD` |\n'
 for r in item['lint_comparison']:
  text+='| '+r['kind']+' | '+('Byte-identical BASE/HEAD outputs' if r['stdout_or_JSON_bytes_exact'] else 'Explicit BASE/HEAD delta; retain both full outputs')+' | `qa/BASE-'+r['kind']+'`, `qa/HEAD-'+r['kind']+'` |\n'
 text+='| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `evidence-inputs.json` and uncapped copied `inputs/` |\n'
 text+='| New screen pairs | PREPARING until completed HEAD minus BASE comparison and every row disposition | ROOT-TO-BIND; no zero-new-pair inference |\n'
 text+='| Publication | PREPARING; records/exchange/bundle binding and dispatch are root-owned | ROOT-TO-BIND |\n\n'
 s=s.replace(mark,text+mark)
 if gate==126:
  s=s.replace('For gate 126 these are selected public AX/ABI consumers of the one local hinit\nchange; no other body is authorized. Other gates\' named target bodies are their\ncomplete source scope.','These three are selected public AX/ABI consumers of the one local hinit change;\nno other body is authorized.')
 else:
  s=s.replace('For gate 126 these are selected public AX/ABI consumers of the one local hinit\nchange; no other body is authorized. Other gates\' named target bodies are their\ncomplete source scope.','These named target bodies are the complete authorized source scope.')
 p.write_text(s)
 (d/'source-evidence-table.md').write_text(text)
pre=Path('/private/tmp/ab34-nword1-replay/PRECHECK-DISPOSITION.json')
if pre.exists():
 d=O/'125/replay-history';d.mkdir(exist_ok=True);(d/pre.name).write_bytes(pre.read_bytes());(d/'README.md').write_text('The original nword1 queue stopped at precheck after a records-only campaign advance. No output tree and no native Lean execution. This is neither a Lean failure nor a passing replay. Await the exact nword2 passing RESULT for HEAD metadata.\n')
 (O/'125/pack-draft.md').write_text((O/'125/pack-draft.md').read_text().replace('## Evidence and its limits','The original word replay queue stopped at precheck, before an output tree or\nnative Lean execution, after a records-only campaign advance. See `replay-history/`.\nIt is neither a Lean failure nor a PASS; only the matching v2 RESULT can bind HEAD.\n\n## Evidence and its limits'))
print('Added exact source/evidence tables to all five drafts and preserved word1 pre-native precheck disposition.')
