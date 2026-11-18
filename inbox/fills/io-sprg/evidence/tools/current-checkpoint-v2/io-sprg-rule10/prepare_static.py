# io-sprg Rule10 preparation, 2026-11-18. No Lean/cache is invoked; exact inventory validation reads Git/source.
# Paths adapted from the bb1-sim exchange suite to the explicitly managed Mac worktree.
# Owner source bytes are read only; output is restricted to --out (default this /tmp staging dir).
import argparse, hashlib, importlib.util, json, re, sys, runpy
from pathlib import Path
sys.dont_write_bytecode = True
DEFAULT_ROOT = '/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange'
ap=argparse.ArgumentParser();ap.add_argument('--root',default=DEFAULT_ROOT)
ap.add_argument('--out',default='/tmp/io-sprg-rule10-prep')
ap.add_argument('--inventory',required=True);args=ap.parse_args()
root=Path(args.root).resolve();out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
builder=root/'evidence/tools/seal/review/archived-gate10-tools/build_seals.py'
spec=importlib.util.spec_from_file_location('read_only_archived_builder',builder)
bs=importlib.util.module_from_spec(spec);spec.loader.exec_module(bs)
iv=runpy.run_path(str(Path(__file__).resolve().parents[1]/'checkpoint_inventory.py'))
inventory=iv['load'](args.inventory,root)
files=[root/f for f in iv['files'](inventory)]
modules={m:root/inventory['owner_sources'][m]['file'] for m in inventory['owners']}
assert set(modules)==set(inventory['owners']) and len(modules)==len(files)
ordered=[];seen=set();active=set()
def visit(m):
 if m in seen:return
 assert m not in active,('import cycle',m)
 active.add(m)
 for dep in bs.header(modules[m].read_bytes())['imports']:
  if dep in modules:visit(dep)
 active.remove(m);seen.add(m);ordered.append(m)
for m in sorted(modules):visit(m)
assert ordered==inventory['owners'],'independent owned topology differs from inventory'
(out/'owners.txt').write_text('\n'.join(ordered)+'\n')
(out/'owner-paths.txt').write_text('\n'.join(m.replace('.','/') for m in ordered)+'\n')
(out/'files.txt').write_text('\n'.join(m.replace('.','/')+'.lean' for m in ordered)+'\n')
# Run-specific collector order is emitted only by orchestrate.py; never publish an old M0 path.
decls=[]
kw=re.compile(r'^((?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)'
 r'(def|abbrev|theorem|lemma|instance|structure|inductive|class|opaque|axiom)\b\s*([^\s(:{\[]*)')
for mod in ordered:
 p=modules[mod];raw=p.read_text();code=bs.blank_comments_strings(raw)
 lines=raw.splitlines();clean=code.splitlines();ns='';scopes=[];local=[]
 for i,line in enumerate(clean):
  n=re.match(r'^namespace\s+(\S+)',line)
  if n:
   scopes.append(('ns',ns));name=n.group(1)
   ns=name[7:] if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]));continue
  if re.match(r'^(?:noncomputable\s+)?section\b',line):scopes.append(('sec',ns));continue
  if re.match(r'^end\b',line):
   if scopes:kind,prev=scopes.pop();ns=prev
   continue
  m=kw.match(line)
  if not m:continue
  flags,kind,name=m.groups()
  if not name or kind=='instance' and name.startswith('['):continue
  full=name[7:] if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]))
  local.append(dict(name=full,kind=kind,private='private' in flags.split(),line=i+1,
   file=p.relative_to(root).as_posix(),module=mod))
 for i,d in enumerate(local):
  end=local[i+1]['line']-1 if i+1<len(local) else len(lines)
  d['text']='\n'.join(lines[d['line']-1:end]);d['end_line']=end;decls.append(d)
byname={d['name']:d for d in decls}
rows=[]
for d in decls:
 if d['private'] or d['kind'] not in ['def','abbrev','instance']:continue
 target=d['name'];base=target.rsplit('.',1)[-1];prefix=target.rsplit('.',1)[0]+'.'
 prefixes=[target+'_',prefix+base[:1].lower()+base[1:]+'_']
 cands=[r for r in decls if r['kind'] in ['theorem','lemma'] and r['module']==d['module']
  and any(r['name'].casefold().startswith(pre.casefold()) for pre in prefixes)
  and re.search(r':=\s*(?:Iff\.)?rfl\b',r['text'])]
 cands.sort(key=lambda r:(not any(r['name']==pre+x for pre in prefixes for x in ['eq','iff']),r['line']))
 row={k:d[k] for k in ['name','kind','line','file','module']}
 row.update(reader=cands[0]['name'] if cands else None,
  reader_line=cands[0]['line'] if cands else None,
  reader_alternatives=[r['name'] for r in cands])
 if d['kind']=='abbrev':row['static_status']='NOTATION_ABBREV_UNSEALABLE'
 elif d['kind']=='instance':row['static_status']='INSTANCE_NEEDS_TERM_AND_PROP_REVIEW'
 elif not cands:row['static_status']='NO_RFL_READER_AUTOMATICALLY_FOUND'
 else:row['static_status']='DRAFT_FULL_READER_TYPE_CONTROL'
 rows.append(row)
manifest=dict(root=str(root),head=inventory['head'],base=inventory['base'],
 inventory_sha256=inventory['inventory_sha256'],owners=ordered,files=[dict(file=p.relative_to(root).as_posix(),
 sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files],
 controls=rows,limitations=['Static use inventory only; term-used subset requires collector ROOT rows.',
 'Draft controls require root-run unsealed and sealed checks; no outcome claimed.',
 'Abbreviations cannot be made irreducible by the canonical harness.',
 'Proof-valued instance bodies are insensitive to rfl because of proof irrelevance.'])
(out/'static-plan.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=1)+'\n')
with(out/'control-candidates.tsv').open('w') as f:
 f.write('target\treader\tstatic_status\tfile:line\n')
 for r in rows:f.write('\t'.join([r['name'],r['reader'] or '',r['static_status'],r['file']+':'+str(r['line'])])+'\n')
print('Owners',len(ordered),'public definition/abbrev/instance candidates',len(rows))
for status in sorted({r['static_status'] for r in rows}):
 print(status,sum(r['static_status']==status for r in rows))
