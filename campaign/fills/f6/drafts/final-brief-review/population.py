from pathlib import Path
import json,re,collections,runpy
OUT=Path(__file__).resolve().parent
# Load only the retained maintainer-owned analyzer; never a delivered script.
v=runpy.run_path(str(OUT/'analyze.py'))
strip_comments=v['strip_comments'];source=v['source'];docs=v['docs'];probe_paths=v['probe_paths'];ROOT=v['ROOT'];WT=v['WT']
index=collections.defaultdict(list)
for module,path in source.items():
 stack=[];parts=[]
 for line_no,line in enumerate(strip_comments(path.read_text()).splitlines(),1):
  t=line.strip()
  ns=re.match(r'^namespace\s+([\w.]+)',t)
  if ns:
   n=ns.group(1);stack.append(('ns',n,list(parts)));parts=n.removeprefix('_root_.').split('.') if n.startswith('_root_.') else parts+n.split('.');continue
  sec=re.match(r'^(?:noncomputable\s+)?section(?:\s+(\w+))?\s*$',t)
  if sec:stack.append(('section',sec.group(1),list(parts)));continue
  en=re.match(r'^end(?:\s+([\w.]+))?\s*$',t)
  if en:
   if stack:
    kind,name,previous=stack.pop();parts=previous
   continue
  mt=re.match(r'^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:noncomputable|private|protected|unsafe)\s+)*)(?:def|abbrev|lemma|theorem|structure|inductive|class)\s+(?P<name>[A-Za-z_][A-Za-z_0-9.\u2080-\u2089\u208a\u208b]*)',t)
  if mt and 'private' not in mt['mods']:
   n='.'.join(parts+[mt['name']]);row={'name':n,'path':str(path.relative_to(WT)),'line':line_no,'module':module};index[n].append(row)
prefixes=['','Turing.','Complexity.','Complexity.TimeHierarchy.','Turing.StepBlock.','Turing.MultiTapeTM.','Turing.FinTM.','Turing.Cfg.']
mentions=collections.defaultdict(list);unresolved=[]
for p in docs+probe_paths:
 text=p.read_text() if p in docs else strip_comments(p.read_text())
 for token in sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9.\u2080-\u2089\u208a\u208b]*',text))):
  token=token.rstrip('.')
  matches=[]
  for prefix in prefixes:
   if prefix+token in index:matches=index[prefix+token];break
  if matches:
   for row in matches:mentions[row['path']].append({'name':row['name'],'line':row['line'],'evidence':str(p.relative_to(ROOT))})
  elif token.startswith(('Turing.','Complexity.')):unresolved.append({'token':token,'evidence':str(p.relative_to(ROOT))})
# Direct imported-definition inventories include model structure fields/generator readers
# that source regex intentionally cannot enumerate. This adds their actual owner homes.
metadata_inputs=[]
for folder,name in [('first-header-preship-v3','First-header-sealed-v3.out'),('header-host-handoff-v4','Final-sealed.out'),('final-seam-preship-v5','Final-sealed.out'),('ledger-contract-preship-v7','Final-sealed.out')]:
 p=OUT.parent/folder/name;metadata_inputs.append(str(p.relative_to(ROOT)))
 for n,owner in re.findall(r'^FOREIGNDEF\|[^|]+\|([^|]+)\|(TCSlib\.[^|]+)\|',p.read_text(),re.M):
  path=owner.replace('.','/')+'.lean';mentions[path].append({'name':n,'evidence':str(p.relative_to(ROOT)),'compiled_owner':True})
# Guard definition names are likewise actual named source/owner data, not imports alone.
for folder in ['layout-preship-v2','first-header-preship-v3','header-host-handoff-v4','final-seam-preship-v5','ledger-contract-preship-v7']:
 for p in (OUT.parent/folder).glob('guard.txt'):
  for token in re.findall(r'(?:Turing|Complexity)\.[A-Za-z_0-9.\u2080-\u2089\u208a\u208b]+',p.read_text()):
   for row in index.get(token,[]):mentions[row['path']].append({'name':row['name'],'line':row['line'],'evidence':str(p.relative_to(ROOT)),'guard':True})
(OUT/'qualified-public-home-index.json').write_text(json.dumps(dict(sorted(index.items())),indent=2)+'\n')
(OUT/'qualified-source-mentions.json').write_text(json.dumps(dict(sorted(mentions.items())),indent=2)+'\n')
(OUT/'unresolved-qualified-tokens.json').write_text(json.dumps(unresolved,indent=2)+'\n')
print('QUALIFIED_CANDIDATES')
for path,rows in sorted(mentions.items()):print(path+' | '+', '.join(sorted({r['name'] for r in rows})[:12]))
