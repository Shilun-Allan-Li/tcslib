"""Read-only supplementary generated-family source attribute inventory.
This does not load 245 compiled namespaces or prove semantic uniqueness.
"""
from pathlib import Path
import subprocess,json,re,hashlib,datetime
P=Path('campaign/gates/117-reading-api/review/source-screen/search')
pins=json.loads((P/'ref-pins.json').read_text())['pins']; trees={}
for row in pins:trees.setdefault(row['tcslib_subtree'],row)
blobs={}
def git(*a):
 p=subprocess.run(['git',*a],capture_output=True)
 if p.returncode not in [0,1]:raise RuntimeError(p.stderr.decode())
 return p.stdout.decode()
for subtree,row in trees.items():
 c=row['commit']
 for line in git('grep','-l','-E','leftCfg|rightCfg|captureCfg',c,'--','TCSlib').splitlines():
  path=line.split(':',1)[1]
  if not path.endswith('.lean'):continue
  b=git('rev-parse',c+':'+path).strip()
  blobs.setdefault(b,{'blob':b,'occurrences':[]})['occurrences'].append({'commit':c,'tcslib_subtree':subtree,'path':path})
records=[]; familydefs=[]
for b,rec in blobs.items():
 text=git('cat-file','blob',b); lines=text.splitlines()
 # All standalone simps commands, retaining multiline continuations until next blank/declaration.
 for i,line in enumerate(lines):
  if re.match(r'^\s*attribute\s+\[simps\b',line):
   j=i+1
   while j<len(lines) and lines[j].strip() and not re.match(r'^\s*(?:/--|(?:private )?(?:def|abbrev|lemma|theorem)|namespace |end )',lines[j]):j+=1
   cmd='\n'.join(lines[i:j])
   if re.search(r'\b(?:leftCfg|rightCfg|captureCfg)\b',cmd):records.append({**rec,'line':i+1,'command':cmd})
  # Prefix at each family definition covers attached attribute immediately before its header.
  if re.search(r'\b(?:def|abbrev)\s+(?:(?:Turing\.)?(?:FinTM\.)?)?(?:leftCfg|rightCfg|captureCfg)\b',line):
   j=i
   while j>0 and (lines[j-1].lstrip().startswith('@[') or (j>i-8 and lines[j-1].strip() and not lines[j-1].rstrip().endswith('-/'))):j-=1
   familydefs.append({**rec,'line':i+1,'prefix':'\n'.join(lines[j:i+1])})
result={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'tcslib_trees':len(trees),'family_candidate_blobs':len(blobs),'matching_standalone_commands':records,'family_definition_prefixes':familydefs,'claim_limit':'Source attributes/standalone simps commands are inspected. This is not compiled namespace inventory for historical trees. Current head compiled-name census is separate parent/sibling evidence.'}
(P/'generated-name-source-check.json').write_text(json.dumps(result,indent=2)+'\n')
print('trees',len(trees),'family blobs',len(blobs),'matching command records',len(records),'definition prefix records',len(familydefs))
seen=set()
for r in records:
 if r['command'] not in seen:print(r['command']);seen.add(r['command'])
for r in familydefs:
 if '@[simps' in r['prefix']:print('attached candidate',r['prefix'])
