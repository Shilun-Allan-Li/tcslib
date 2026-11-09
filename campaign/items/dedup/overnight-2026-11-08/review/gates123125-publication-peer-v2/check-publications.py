import hashlib,json,subprocess,re,os
from pathlib import Path
B=Path('/private/tmp/ab34-gates123125-peer-v2');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');PUB=json.loads((B/'inputs/publications.json').read_text());reports=[]
def git(*args):return subprocess.run(['git','-C',str(R),*args],capture_output=True,check=True).stdout
X=Path(os.environ['TCSLIB_EXCHANGE'])
def xgit(*args):return subprocess.run(['git','-C',str(X),*args],capture_output=True,check=True).stdout
def sha(x):return hashlib.sha256(x).hexdigest()
for p in PUB:
 gate=p['gate'];prefix=f'campaign/gates/{gate}-{p["slug"]}';dest=B/str(gate);dest.mkdir(exist_ok=True);(dest/'published').mkdir(exist_ok=True);pins={}
 for role in ['source','records','exchange']:
  readgit=xgit if role=='exchange' else git; pins[role]=readgit('rev-parse','--verify',p[role]+'^{commit}').decode().strip();readgit('cat-file','-e',pins[role]+'^{commit}');assert pins[role]==p[role]
 for name in ['publication.json','prompt.md','BUNDLE-FILES.txt']:(dest/'published'/name).write_bytes((R/prefix/name).read_bytes())
 paths=(R/prefix/'BUNDLE-FILES.txt').read_text().splitlines();assert len(paths)==len(set(paths))==p['sections'];parts=[];rows=[]
 for path in paths:
  rev=pins['source'] if path.startswith('TCSlib/') else pins['records'];raw=git('show',rev+':'+path);text=raw.decode('utf-8');out=dest/'sections'/path;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
  text+=' ' if False else ('' if text.endswith('\n') else '\n')
  if path.endswith('.lean') or path.endswith('.py'):text='```\n'+text+'```\n'
  parts.append(f'## ===== {path} =====\n\n'+text);rows.append({'path':path,'read_commit':rev,'bytes':len(raw),'sha256':sha(raw)})
 expected='\n'.join(parts).encode('utf-8');bundle=f'{gate}-{p["slug"]}-bundle.md';actual=xgit('show',pins['exchange']+':'+p['folder']+'/'+bundle);assert actual==expected and len(actual)==p['bytes'] and sha(actual)==p['sha256'];(dest/'published'/bundle).write_bytes(actual)
 heads=[x[9:-6] for x in actual.decode().splitlines() if x.startswith('## ===== ') and x.endswith(' =====')];assert heads==paths
 for name in ['README.md','BUNDLE-FILES.txt','SHA256SUMS']:(dest/'published'/('exchange-'+name)).write_bytes(xgit('show',pins['exchange']+':'+p['folder']+'/'+name))
 assert (dest/'published/exchange-BUNDLE-FILES.txt').read_bytes()==(dest/'published/BUNDLE-FILES.txt').read_bytes()
 for line in (dest/'published/exchange-SHA256SUMS').read_text().splitlines():
  digest,name=line.split(maxsplit=1);target=dest/'published'/(bundle if name==bundle else 'exchange-'+name);assert sha(target.read_bytes())==digest
 prompt=(dest/'published/prompt.md').read_text();readme=(dest/'published/exchange-README.md').read_text();canonical=json.loads((dest/'published/publication.json').read_text());assert all(canonical[k]==v for k,v in p.items())
 for key in ['source','records']:assert p[key] in readme and p[key] in prompt
 assert p['exchange'] in prompt and p['sha256'] in prompt and p['sha256'] in readme and str(p['sections']) in prompt
 assert f'{p["bytes"]:,}' in prompt and f'gate{gate}-{p["slug"]}-findings.md' in prompt
 pack=(dest/'sections'/prefix/'pack.md').read_text();assert not re.search(r'ROOT[-_ ](?:TO[-_ ]BIND|FINAL|FILL)|⟨ROOT',pack+'\n'+prompt)
 if gate==123:assert 'earlier359-section gate123 prompt is VOID' in prompt
 anchorprefix='campaign/status/2026-11-08-mig1-merge';anchors={n:json.loads((dest/'sections'/anchorprefix/n).read_text()) for n in ['receipt.json','object-hashes.json','Lean-tree.json']};tools=dest/'sections'/prefix/'reproduction-tools';context=json.loads((tools/'context.json').read_text());assert sha((tools/'staticsorry.py').read_bytes())==context['actual_static_helper_sha256'] if gate==123 else sha((tools/'staticsorry.py').read_bytes())==context['static_helper_sha256']
 assert len(anchors['object-hashes.json'])==895 and len(anchors['Lean-tree.json'])==1003
 for name in ['context.json','env.sh.example','leanelab.sh','staticsorry.py','copy-text-screen-v3.py','campaign_style_lint.py','style_lint.py','declfreeze.py','pairdiff.py','lean-toolchain','lake-manifest.json']:assert (tools/name).is_file()
 req=json.loads((dest/'sections'/prefix/'review/screen/HEAD-request.json').read_text());assert sha((tools/'copy-text-screen-v3.py').read_bytes())==req['tool_sha256']
 review=dest/'sections'/prefix/'review';m=json.loads((review/'MANIFEST.json').read_text())
 for row in m['files']:
  raw=(review/row['path']).read_bytes();assert len(raw)==row['bytes'] and sha(raw)==row['sha256']
 report={'gate':gate,'pins_verified':pins,'all_sections_exact_byte_rebuild':True,'section_count':len(paths),'bundle_bytes':len(actual),'bundle_SHA256':sha(actual),'exchange_readme_and_SHA256SUMS_pass':True,'issued_prompt_bindings_pass':True,'both_full_source_records_pins_and_findings_routing_exact':True,'canonical_pack_prompt_no_ROOT_placeholders':True,'MAC8_three_anchors_present_full':True,'all_required_reproduction_helpers_present':True,'exact_screen_helper_hash_matches_request':True,'static_helper_hash_matches_context':True,'full_frozen_review_payload_hashes_exact':len(m['files']),'sections':rows};(dest/'PUBLICATION-CHECK.json').write_text(json.dumps(report,indent=2)+'\n');reports.append({k:v for k,v in report.items() if k!='sections'})
(B/'PUBLICATION-SUMMARY.json').write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps(reports,indent=2))
