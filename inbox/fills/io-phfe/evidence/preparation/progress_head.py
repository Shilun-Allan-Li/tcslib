"""Inventory exact committed proof admissions and new completions; starts no Lean."""
from pathlib import Path
import ast,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
out=Path(sys.argv[1]);oldhead=sys.argv[2];out.mkdir(parents=True,exist_ok=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
canonical=Path('evidence/preparation/tools/seal/review/touched.py');tree=ast.parse(canonical.read_text());keep=[]
for n in tree.body:
 if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef)):keep.append(n)
 elif isinstance(n,ast.Assign) and all(isinstance(t,ast.Name) and t.id in ['KW','DECL','TOP'] for t in n.targets):keep.append(n)
ns={};exec(compile(ast.Module(body=keep,type_ignores=[]),str(canonical),'exec'),ns)
spec=importlib.util.spec_from_file_location('lex','evidence/preparation/tools/seal/review/archived-gate10-tools/scan_explicit.py');lex=importlib.util.module_from_spec(spec);spec.loader.exec_module(lex)
def show(rev,f):
 p=subprocess.run(['git','show',rev+':'+f],capture_output=True);return p.stdout.decode() if p.returncode==0 else None
def admitted(s):return bool(re.search(r'\b(?:sorry|admit)\b',lex.blank(s)))
files=subprocess.check_output(['git','diff','--name-only',base,head,'--','TCSlib'],text=True).splitlines();by={};proofs=[];admissions=[]
for f in files:
 raw=show(head,f);assert raw is not None
 old=show(oldhead,f);a={d['name']:d for d in ns['decls'](old)} if old else {}
 count=len(re.findall(r'\b(?:sorry|admit)\b',lex.blank(raw)))
 by[f]={'lines':len(raw.splitlines()),'direct_admissions':count,'git_source_sha256':hashlib.sha256(raw.encode()).hexdigest()}
 for d in ns['decls'](raw):
  if admitted(d['text']):admissions.append({'file':f,'name':d['name'],'line':d['decl_line']})
  elif d['kind'] in ['theorem','lemma'] and (d['name'] not in a or admitted(a[d['name']]['text'])):
   proofs.append({'file':f,'name':d['name'],'new_helper':d['name'] not in a})
meta={'head':head,'comparison_head':oldhead,'source_mode':'git show exact committed snapshot','files':len(files),'lines':sum(v['lines'] for v in by.values()),'direct_admissions':sum(v['direct_admissions'] for v in by.values()),'by_file':by}
(out/'progress.json').write_text(json.dumps(meta,indent=2)+'\n');(out/'proved.json').write_text(json.dumps(proofs,indent=2)+'\n');(out/'admissions.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in admissions))
print(json.dumps({k:v for k,v in meta.items() if k!='by_file'}));print('newly_completed',len(proofs))
