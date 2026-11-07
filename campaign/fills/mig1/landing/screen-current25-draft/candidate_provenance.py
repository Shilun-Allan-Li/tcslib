"""Resolve newly labelled candidate endpoints to explicit baseline move origins."""
from pathlib import Path
import ast, json, re
p=Path(__file__).resolve().parent
idx={label:json.loads((p/(label+'-screen-index.json')).read_text()) for label in ['base','head']}
base_pairs={(r['target'],r['source']) for r in json.loads((p/'base-all-candidates.json').read_text())}
ns={'re':re};tree=ast.parse((p/'copy-text-screen-v3.py.txt').read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['strip','body']],type_ignores=[]),'<reviewed-parser-body>','exec'),ns)
def code(label,key):
 r=idx[label][key];raw=(p/'inputs'/label/(r['path']+'.txt')).read_text()[r['raw_start']:r['raw_end']]
 return ns['strip'](raw)
def norm(s):return re.sub(r'\s+','',s)
def origin(key):
 if key.startswith('Primitives.lean::fwdMap'):
  candidate='Catalog.lean::'+key.split('::')[1].replace('fwdMap','a2_map',1)
  if candidate in idx['base']:return candidate
 return key if key in idx['base'] else None
rows=[]
for i,row in enumerate(json.loads((p/'new-all.json').read_text()),1):
 r=dict(row,id=f'N{i:02d}')
 for endpoint in ['target','source']:
  key=r[endpoint];o=origin(key);r[endpoint+'_baseline_screen_origin']=o
  if o:
   before=ns['body'](code('base',o)).replace('a2_map','fwdMap').replace('A2MapState','FwdMapState')
   after=ns['body'](code('head',key))
   r[endpoint+'_normalized_body_equal_after_explicit_move_renames']=norm(before)==norm(after)
 r['origin_pair_already_reported_in_baseline']=(r['target_baseline_screen_origin'],r['source_baseline_screen_origin']) in base_pairs
 rows.append(r)
(p/'new-candidate-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
for r in rows:
 print(r['id'],r['target'],'<-',r['source'],'ORIGIN_PAIR',r['origin_pair_already_reported_in_baseline'],r['target_baseline_screen_origin'],r['source_baseline_screen_origin'])
