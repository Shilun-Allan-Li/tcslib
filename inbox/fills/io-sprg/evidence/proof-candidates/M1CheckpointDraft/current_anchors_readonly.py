"""Source declaration/field anchors and verbatim archived tables. No Lean or git."""
from pathlib import Path
import csv,hashlib,json,re
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
b=Path('/private/tmp/io-sprg-proof-notes/M1CheckpointDraft')
snapshot=json.loads((b/'snapshot.json').read_text())
# Keep nested comments/string contents from creating false declaration commands.
ns={};exec((b/'snapshot_readonly.py').read_text().split('oldhash={}')[0],ns)
strip=ns['strip']
rows=[]
for info in snapshot['files']:
 p=repo/info['file'];lines=strip(p.read_text()).splitlines();stack=[];structure=None
 for i,line in enumerate(lines,1):
  m=re.match(r'^(namespace|section)\b(?:\s+([^\s]+))?',line)
  if m:
   stack.append((m[1],m[2]or''));structure=None;continue
  if re.match(r'^end(?:\s|$)',line):
   if stack:stack.pop()
   structure=None;continue
  prefix='.'.join(n for k,n in stack if k=='namespace')
  m=re.match(r'^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)',line)
  if m:
   kind,name=m.groups();full=prefix+'.'+name if prefix else name
   rows.append({'name':full,'kind':kind,'file':info['file'],'line':i})
   structure=full if kind in('structure','class')else None
   continue
  if structure:
   field=re.match(r'^  ([^\s:(){}]+)\s*(?::|[({])',line)
   if field and not field[1].startswith(('--','/-','@')):
    rows.append({'name':structure+'.'+field[1],'kind':'structure-field',
      'file':info['file'],'line':i})
lookup={r['name']:r for r in rows}
assert len(lookup)==len(rows),(len(rows),len(lookup))
with(b/'current-declaration-anchors.tsv').open('w')as f:
 w=csv.DictWriter(f,fieldnames=['name','kind','file','line'],delimiter='\t');w.writeheader();w.writerows(rows)
(b/'current-declaration-anchors.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
archive=repo/'evidence/checkpoints/M0/REPORT.md';text=archive.read_text();ls=text.splitlines(keepends=True)
headers=[('fidelity','| Paper item / page |'),('rule15','| Primitive / algorithm layer |'),
 ('target-selection','| Field / consequence |'),('nonvacuity','| Object | Source witness')]
chunks=[];binding=[]
for name,start in headers:
 i=next(j for j,l in enumerate(ls)if l.startswith(start));j=i
 while j<len(ls)and ls[j].startswith('|'):j+=1
 block=''.join(ls[i:j]);chunks.append((name,block))
 binding.append({'name':name,'archive':str(archive.relative_to(repo)),
 'archive_start_line':i+1,'archive_end_line':j,'sha256':hashlib.sha256(block.encode()).hexdigest(),
 'lines':j-i})
start=text.index('## Phase B target statements (unproved)')
end=text.index('## Headline axiom prints at M0',start)
targets=text[start:end].rstrip()+'\n'
(b/'archived-tables.md').write_text('\n\n'.join('### Archived M0 '+name+' table\n\n'+block.rstrip()for name,block in chunks)+'\n')
(b/'archived-target-definitions.md').write_text(targets)
(b/'archived-table-bindings.json').write_text(json.dumps({'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'tables':binding,'target_definitions_sha256':hashlib.sha256(targets.encode()).hexdigest()},indent=2)+'\n')
# All explicitly named table entries that resolve to current owned declarations/fields.
base='TCSlib.Cryptography.Obfuscation.StructuredSeed.'
selected={}
for _,block in chunks:
 for token in re.findall(r'`([^`]+)`',block):
  for name in (token,base+token):
   if name in lookup:selected[name]=lookup[name]
# Include all structure fields so shorthand field names in Rule15/non-vacuity resolve.
for row in rows:
 if row['kind']=='structure-field':selected[row['name']]=row
# Explicit current entry points that matter to changed M1 proof status.
for short in('Internal.encodeList_injective_of_fixedWidth','Internal.encodeList_length_of_fixedWidth',
 'Params.G4_seed_allOutputs','SPRG.Raw.HasComplexityEff.hasComplexity','Params.primeWidthBound'):
 selected[base+short]=lookup[base+short]
md=['## Current declaration anchors for the archived tables\n',
 'The tables above preserve M0 bytes and therefore retain HISTORICAL line references.\n',
 'This appendix gives current M1 anchors by declaration identity. The adjacent TSV\n',
 'contains every explicit owned declaration and structure field; generated constructors,\n',
 'recursors and inherited fields remain represented by their owning structure. This is\n',
 'a source anchor index, not a replacement for the final typed kernel census.\n\n',
 '| Current full name (area prefix omitted) | M1 source anchor |\n',
 '| --- | --- |\n']
for name,row in sorted(selected.items()):
 short=name.removeprefix(base);path=row['file'].split('/StructuredSeed/',1)[-1]
 md.append(f"| `{short}` | `{path}:{row['line']}` |\n")
(b/'current-anchor-appendix.md').write_text(''.join(md))
print('Current source anchors:',len(rows),'table named anchors:',len(selected),'verbatim archive tables:',len(chunks))
