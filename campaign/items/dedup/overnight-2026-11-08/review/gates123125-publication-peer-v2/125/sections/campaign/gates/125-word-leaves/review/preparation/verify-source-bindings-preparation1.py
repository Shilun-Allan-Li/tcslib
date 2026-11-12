from pathlib import Path
import json,re,hashlib,difflib
O=Path('/private/tmp/ab34-small-gate-drafts');S=json.loads((O/'scope.json').read_text());F=Path('/private/tmp/ab34-ro1-integration')
raw=(F/'freeze-declarations.py').read_text();ns={};exec(raw[:raw.index('changed=[];removed=[]')],ns);extract=ns['extract']
for item in S['items']:
 gate=item['gate'];d=O/str(gate);rel=item['owner'];a=(d/'source/BASE'/(rel+'.txt')).read_text();b=(d/'source/HEAD'/(rel+'.txt')).read_text();ad={r['name']:r for r in extract(a)};bd={r['name']:r for r in extract(b)}
 assert set(ad)==set(bd),(gate,set(ad)^set(bd));changes=[]
 for name in ad:
  assert ad[name]['header']==bd[name]['header'],(gate,name)
  if ad[name]['body']!=bd[name]['body']:changes.append(name)
 expected=item['source_freeze']['rows'][0]['changed_chunks'];assert set(changes)==set(expected),(gate,changes,expected)
 aa=a;bb=b
 for name in changes:
  x,y=ad[name],bd[name];assert aa.count(x['full'])==bb.count(y['full'])==1
  marker='DECLARATION_BODY_SLOT '+name;aa=aa.replace(x['full'],marker);bb=bb.replace(y['full'],marker)
 assert aa==bb,(gate,'outside selected declaration chunks differs')
 literals=[]
 if gate==123:
  info=json.loads((d/'inputs/ab34-ch7-run-seals-v2/SOURCE.json').read_text());assert info['source_commit']==item['head'];assert info['owner_sha256']==hashlib.sha256(b.encode()).hexdigest()
  for name,chunk in info['complete_literal_chunks'].items():assert b.count(chunk)==1;literals.append({'name':name,'chunk_sha256':hashlib.sha256(chunk.encode()).hexdigest(),'literal_HEAD_count':1})
 elif gate in [124,125]:
  data=json.loads((d/'inputs/sg-extras/chunk-mappings.json').read_text())
  for r in data:
   if r['path']!=rel:continue
   assert b.count(r['new_chunk'])==1;literals.append({'name':r['name'],'chunk_sha256':hashlib.sha256(r['new_chunk'].encode()).hexdigest(),'literal_HEAD_count':1})
 elif gate==126:
  chunk=(d/'inputs/rs1/hinit-after.lean.txt').read_text();assert b.count(chunk)==1;literals.append({'name':'hinit inside Turing.exists_selfStartupTMK','chunk_sha256':hashlib.sha256(chunk.encode()).hexdigest(),'literal_HEAD_count':1})
 elif gate==127:
  chunk=(d/'inputs/nat-reader/canonOffset_spec-HEAD.lean.txt').read_text();assert b.count(chunk.strip())==1;literals.append({'name':'Turing.MachineFormat.canonOffset_spec','chunk_sha256':hashlib.sha256(chunk.encode()).hexdigest(),'literal_HEAD_count':1})
 # Literal source comparison is stronger than a claim inferred merely from
 # unchanged imported theorem names, while remaining a source (not global env)
 # statement. Full compiled ABI/AX is a separate selected-root check.
 attrs=lambda s:re.findall(r'^\s*(?:attribute\b.*|@\[[^\n]*)',s,re.M)
 imports=lambda s:re.findall(r'^import[^\n]*',s,re.M)
 receipt={'gate':gate,'source_base':item['base'],'source_head':item['head'],'BASE_sha256':hashlib.sha256(a.encode()).hexdigest(),'HEAD_sha256':hashlib.sha256(b.encode()).hexdigest(),'all_source_declaration_names_exact':True,'all_retained_literal_headers_exact':True,'all_outside_changed_declaration_chunks_byte_exact':True,'changed_declarations_exact':changes,'all_source_import_lines_exact':imports(a)==imports(b),'all_source_attribute_lines_exact':attrs(a)==attrs(b),'literal_claimed_scope_chunks_match_HEAD':literals,'default_simp_argument':'No source import/attribute changes, full outside-target source exact; selected native simp flags compared separately. No full generated/global simp metadata equality inferred.'}
 (d/'literal-source-and-scope-binding.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('gate',gate,'literal source/freeze/scope binding PASS',len(literals))
