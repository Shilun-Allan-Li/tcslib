"""Freeze public and private source headers/prose; proof sketches may change.
Non-theorem definitions and structure fields are conservatively frozen in full.
Adds helper declarations permissibly, while detecting removed/changed existing entries.
"""
from pathlib import Path
import ast, hashlib, importlib.util, json, re, subprocess, sys
sys.dont_write_bytecode=True
# Load only the unchanged canonical pure declaration parser, without its CLI driver.
canonical=Path('evidence/preparation/tools/seal/review/touched.py')
tree=ast.parse(canonical.read_text()); keep=[]
for node in tree.body:
 if isinstance(node,(ast.Import,ast.ImportFrom,ast.FunctionDef)):keep.append(node)
 elif isinstance(node,ast.Assign) and all(isinstance(t,ast.Name) and t.id in ['KW','DECL','TOP'] for t in node.targets):keep.append(node)
ns={};exec(compile(ast.Module(body=keep,type_ignores=[]),str(canonical),'exec'),ns)

def record(src):
 out={}
 for d in ns['decls'](src):
  text=d['text']; prose=''
  if text.startswith('/--'):
   e=text.index('-/')+2;doc=text[3:e-2]
   prose=doc.split('**Proof sketch.**',1)[0].rstrip()
   text=text[e:].lstrip()
  if d['kind'] in ['theorem','lemma']:
   # In this source collection every theorem uses an explicit := delimiter.
   # Search outside comments/strings and balanced binder brackets.
   spec=importlib.util.spec_from_file_location('lex','evidence/preparation/tools/seal/review/archived-gate10-tools/scan_explicit.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
   mask=m.blank(text);depth=0;cut=None
   for i,c in enumerate(mask):
    if c in '([{⟨':depth+=1
    elif c in ')]}⟩':depth-=1
    elif depth==0 and mask.startswith(':=',i):cut=i;break
   if cut is None:raise RuntimeError('theorem without body delimiter: '+d['name'])
   text=text[:cut]
  out[d['name']]={'kind':d['kind'],'private':d['private'],'prose':prose,'header':text.strip()}
 return out

def snapshot(files):return {f:record(Path(f).read_text()) for f in files}
def compare(old,new):
 changes=[];helpers=[]
 for f,rows in old.items():
  if f not in new:changes.append([f,'REMOVED_FILE']);continue
  for n,r in rows.items():
   if n not in new[f]:changes.append([f,n,'REMOVED'])
   elif r!=new[f][n]:changes.append([f,n,'CHANGED'])
 for f,rows in new.items():
  for n in rows:
   if n not in old.get(f,{}):helpers.append([f,n])
 return changes,helpers

def main():
 mode,path=sys.argv[1:3];p=Path(path)
 files=Path('evidence/logs/owned-files.txt').read_text().splitlines()
 current=snapshot(files)
 if mode=='write':
  obj={'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'files':current,'parser_sha256':hashlib.sha256(canonical.read_bytes()).hexdigest()}
  p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
  # Controls run against cloned in-memory records, never live source.
  f=next(f for f,rs in current.items() if any(r['kind']=='theorem' and r['prose'] for r in rs.values()));n=next(n for n,r in current[f].items() if r['kind']=='theorem' and r['prose'])
  results={}
  for label,field in [('one_character_header','header'),('prose_before_sketch','prose')]:
   edited=json.loads(json.dumps(current));edited[f][n][field]+='X';ch,_=compare(current,edited);results[label]={'expected_check_pass':False,'check_pass':not bool(ch),'detected':ch}
  src=Path(f).read_text(); mutated=src.replace('/--','/--X',1)
  rs=record(mutated);ch,_=compare({f:current[f]},{f:rs});results['source_prose_edit_with_sketch_present']={'expected_check_pass':False,'check_pass':not bool(ch),'detected':ch}
  p.with_suffix('.controls.json').write_text(json.dumps(results,indent=2)+'\n');assert all(not x['check_pass'] for x in results.values())
  print('FROZEN',sum(map(len,current.values())),'declarations; all negative controls rejected')
 elif mode=='check':
  old=json.loads(p.read_text());changes,helpers=compare(old['files'],current);print(json.dumps({'frozen_head':old['head'],'changes':changes,'helpers':helpers,'pass':not changes},indent=2));raise SystemExit(bool(changes))
 else:raise SystemExit('mode must be write or check')
if __name__=='__main__':main()
