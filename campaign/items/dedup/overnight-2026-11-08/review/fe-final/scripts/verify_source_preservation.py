from pathlib import Path
import json,hashlib,sys
sys.dont_write_bytecode=True
O=Path('/private/tmp/ab34-fe-live1-final-validation');E=O/'evidence';OLD=Path('/private/tmp/ab34-overnight-fe1/EXPORT');sys.path.insert(0,str(E/'helpers/devtools/seyoon'));from graph import imports_of
maps=json.loads((OLD/'DRAFT-SOURCE-MAP.json').read_text());src=json.loads((E/'SOURCE.json').read_text());rows=[]
for r in src['files']:
 p=r['path'];body=(OLD/'draft-source'/(p+'.txt')).read_text();restored=body
 for m in [m for m in maps if m['path']==p]:
  new=(OLD/m['new_chunk']).read_text();old=(OLD/m['old_chunk']).read_text();assert restored.count(new)==1,(p,m['name']);restored=restored.replace(new,old)
 base=(E/'source/BASE'/(p+'.txt')).read_text();headfile=E/'source/HEAD'/(p+'.txt');basefile=E/'source/BASE'/(p+'.txt');assert restored==base,(p,'non-target source bytes differ')
 assert imports_of(basefile)==imports_of(headfile)
 rows.append({'path':p,'all_bytes_outside11_prior_body_replacements_exact_BASE':True,'final_code_token_equivalence_reference':'CODE-CORRESPONDENCE.json','BASE_imports':imports_of(basefile),'HEAD_imports':imports_of(headfile),'imports_exact':True})
(E/'SOURCE-PRESERVATION.json').write_text(json.dumps({'PASS':True,'rows':rows,'new_public_API_or_name_or_import_or_home_or_debt_permission':False},indent=2)+'\n');print('PASS: all other source bytes and all five import headers exact; final code token correspondence separately checked')
