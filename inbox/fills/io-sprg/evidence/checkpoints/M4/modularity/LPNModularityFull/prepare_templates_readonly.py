"""Prepare complete tactic-free old-declaration LPN split templates in temp only.

No Lean/Git/cache/source edits. Pure reviewed parser definitions are extracted
without running either parser CLI. New helper bodies/statements are not inserted.
"""
from pathlib import Path
import ast
import csv
import hashlib
import io
import json
import re

W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
P=Path('/private/tmp/io-sprg-proof-notes/LPNModularity')
B=Path('/private/tmp/io-sprg-proof-notes/LPNModularityFull')
OLD='TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN.lean'
PREFIX='TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN'
DEST='TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/'
HEAD='04249b85e80a007dc5845077a18a365d5150e14b'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
source=(W/OLD).read_bytes();text=source.decode();lines=text.splitlines(keepends=True)
plan=json.loads((P/'move-boundaries.json').read_text())
assert sha(source)==plan['source_sha256']=='e7c468cbe10b2744e507a63c48da4029a2f51fcf13ce34fb8a8793b89a7e08bd'
assert len(lines)==428
current_all=json.loads((W/'evidence/checks/m3-final-v2/global-freeze/current-global-map.json').read_text())
frozen_all=json.loads((W/'evidence/checks/m3-final-v2/global-freeze/frozen-global-map.json').read_text())
old={n:r for n,r in current_all.items() if r['file']==OLD};assert len(old)==42
assert all(n in frozen_all and old[n]['header_sha256']==frozen_all[n]['header_sha256'] and
 old[n]['prose_prefix_sha256']==frozen_all[n]['prose_prefix_sha256'] for n in old)

# Extract pure parser definitions/regex constants; neither CLI/top-level Git loop runs.
def pure(path, functions, constants):
 tree=ast.parse(path.read_text(),filename=str(path));nodes=[]
 for node in tree.body:
  if isinstance(node,(ast.Import,ast.ImportFrom)):nodes.append(node)
  elif isinstance(node,ast.FunctionDef) and node.name in functions:nodes.append(node)
  elif isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id in constants for t in node.targets):nodes.append(node)
 env={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(path),'exec'),env);return env
lex=pure(W/'evidence/tools/seal/decls2.py',{'strip','decls'},{'KW'})
clash=pure(W/'evidence/tools/clash/clash_scan.py',{'strip_code','parse_decls'},
 {'KINDS','MODS','ATTR','DECL_RE','NAME_RE'})
doc=pure(W/'evidence/tools/freeze_global.py',{'doc_prefix'},set())['doc_prefix']

def chunk(lo,hi):return ''.join(lines[lo-1:hi])
# Existing statement/docstring/body ranges exactly as the already-reviewed plan.
ranges={'Defs':[[49,361],[408,424]],'Encoding':[[363,386]],'Transport':[],'Hop':[[388,406]]}
headers={}
oldrefs=text.split('## References\n',1)[1].split('**Deviations.**',1)[0]
for leaf in ['Defs','Encoding','Transport','Hop']:
 header=(P/(leaf+'.header.lean.txt')).read_text()
 # Use the full existing bibliography in the NEW child headers. Old declaration
 # docstrings and the compatibility facade's original module prose stay exact.
 a=header.index('## References\n');b=header.index('**Deviations.**',a)
 header=header[:a]+'## References\n'+oldrefs+header[b:]
 headers[leaf]=header
texts={}
marker='-- MOVE THE RECORDED COMMAND BLOCKS HERE; NO NEW DEFINITIONS.'
for leaf in ['Defs','Encoding']:
 body='\n'.join(chunk(a,b) for a,b in ranges[leaf])
 assert marker in headers[leaf]
 texts[leaf]=headers[leaf].replace(marker,body.rstrip())
# Transport intentionally has no new statement or placeholder term: a compilable
# empty owner ready for one-at-a-time specialized helper additions after the move.
texts['Transport']=headers['Transport'].replace(marker,
 '-- Specialized existing-library transport helpers may be added here after the mechanical split.')
# Planned helper group05–09 lives in Internal, but no unproved new helper is added.
# The only current declaration is the unchanged Params.lpn_hop stub.
hopbody=chunk(388,406)
oldfooter='end Internal\n\nend TCSlib.Cryptography.Obfuscation.StructuredSeed\n'
assert headers['Hop'].endswith(oldfooter)
texts['Hop']=headers['Hop'][:-len(oldfooter)].replace(marker,
 '-- Specialized pointwise/section/averaging helpers may be added here after the split.')
texts['Hop']+='end Internal\n\nnamespace Params\n\n'+hopbody+'\nend Params\n\nend TCSlib.Cryptography.Obfuscation.StructuredSeed\n'
# Preserve the original compatibility module docstring verbatim. A second module
# docblock adds the explicit facade Contents; it introduces no declaration.
module_doc=text[text.index('/-!'):text.index('-/',text.index('/-!'))+2]
pre=text[:text.index('/-!')]
pre=re.sub(r'^import .*\n','',pre,flags=re.M)
insert_at=pre.index('set_option')
pre=pre[:insert_at]+''.join('import '+m+'\n' for m in plan['proposed_imports'][PREFIX])+'\n'+pre[insert_at:]
# Avoid an accidental blank import block left where the original two imports stood.
pre=pre.replace('-/\n\n\nimport','-/\nimport').replace('-/\n\nimport','-/\nimport')
texts['Facade']=pre+module_doc+'''

/-!
## Contents

* `LPN.Defs`: all original challenge/advice/reduction definitions, instances and exact readers.
* `LPN.Encoding`: the three original injectivity and polynomial advice-bound statements.
* `LPN.Transport`: the specialized transport helper owner, initially empty.
* `LPN.Hop`: the unchanged every-realizer hop statement and future specialized proof glue.

Every old full name, definition, reader, theorem header and statement docstring is retained.
-/
'''
assert module_doc in texts['Facade']
paths={leaf:DEST+leaf+'.lean' for leaf in ['Defs','Encoding','Transport','Hop']};paths['Facade']=OLD
maps={};allrows=[]
for leaf,src in texts.items():
 assert len(src.splitlines())<=1000 and max(map(len,src.splitlines()),default=0)<=100
 assert not re.search(r'\bby\b','\n'.join(clash['strip_code'](src))),leaf
 parsed=clash['parse_decls'](src);heads=lex['decls'](src)
 assert set(heads)=={r['full'] for r in parsed}
 for name,(kind,line,header) in heads.items():
  assert name not in maps,'duplicate moved FQN'
  prose=doc(src,line)
  maps[name]={'file':paths[leaf],'line':line,'kind':kind,'header':header,
   'header_sha256':sha(header.encode()),'statement_prose':prose,'prose_sha256':sha(prose.encode())}
 (B/(leaf+'.lean.template')).write_text(src)
assert set(maps)==set(old),'missing or newly introduced declaration'
assert len(lex['decls'](texts['Defs']))==38 and len(lex['decls'](texts['Encoding']))==3
assert len(lex['decls'](texts['Hop']))==1 and not lex['decls'](texts['Transport']) and not lex['decls'](texts['Facade'])

# A command includes the original attached docstring, and stops before the next
# command's attached docstring. Trim only separator newlines for its checksum.
starts=sorted((r['line'],n) for n,r in old.items())
def doc_start(raw,number):
 ls=raw.splitlines();j=number-2
 while j>=0 and not ls[j].strip():j-=1
 if j>=0 and ls[j].rstrip().endswith('-/'):
  while j>=0 and not ls[j].startswith('/--'):j-=1
  assert j>=0
  return j+1
 return number
ledger=[]
for index,(start,name) in enumerate(starts):
 row=old[name];new=maps[name];leaf=new['file'].rsplit('/',1)[-1][:-5]
 ds=doc_start(text,start)
 end=doc_start(text,starts[index+1][0])-1 if index+1<len(starts) else 424
 block=''.join(lines[ds-1:end]).rstrip('\n')+'\n'
 dest=texts[leaf];assert dest.count(block)==1,(name,'full command/doc block not exact')
 assert new['kind']==row['kind'] and new['header_sha256']==row['header_sha256']
 assert new['prose_sha256']==row['prose_prefix_sha256']
 command=''.join(lines[start-1:end]).rstrip('\n')+'\n'
 attached=''.join(lines[ds-1:start-1])
 record={'name':name,'old_file':OLD,'new_file':new['file'],'kind':row['kind'],
  'old_start':start,'old_doc_start':ds,'old_end':end,'new_start':new['line'],
  'target_module':new['file'][:-5].replace('/','.'),
  'frozen_header_sha256':frozen_all[name]['header_sha256'],'current_header_sha256':new['header_sha256'],
  'frozen_statement_prose_sha256':frozen_all[name]['prose_prefix_sha256'],'current_statement_prose_sha256':new['prose_sha256'],
  'full_docstring_sha256':sha(attached.encode()),'command_sha256':sha(command.encode()),
  'doc_and_command_block_sha256':sha(block.encode()),'complete_command_and_doc_moves_verbatim':True,
  'existing_proof_or_stub_unchanged':True}
 ledger.append(record)
assert len(ledger)==42
(B/'existing-declaration-move-map.json').write_text(json.dumps(ledger,indent=2)+'\n')
buf=io.StringIO();wr=csv.DictWriter(buf,fieldnames=list(ledger[0]),delimiter='\t',lineterminator='\n');wr.writeheader();wr.writerows(ledger)
(B/'existing-declaration-move-map.tsv').write_text(buf.getvalue())
(B/'template-current-global-map.json').write_text(json.dumps(maps,indent=2,ensure_ascii=False)+'\n')
(B/'new-helper-placement.tsv').write_bytes((P/'new-helper-placement.tsv').read_bytes())
summary={'status':'COMPLETE_TEMP_TEMPLATES_STATIC_ONLY_NOT_APPLIED_NOT_COMPILED',
 'source_head_supplied_by_root':HEAD,'source_file':OLD,'source_sha256':sha(source),'source_lines':428,
 'original_top_level_names':42,'Defs_names':38,'Encoding_names':3,'Hop_names':1,'Transport_names':0,
 'facade_names':0,'exact_old_names_preserved':True,'all_M0_headers_prose_preserved':True,
 'all_complete_old_commands_docs_bodies_stubs_verbatim':True,'new_theorems_or_definitions':0,
 'new_tactic_blocks':0,'source_tactic_blocks':0,'unchanged_original_sorry_count':4,
 'template_sorry_count':sum(len(re.findall(r'\bsorry\b','\n'.join(clash['strip_code'](v)))) for v in texts.values()),
 'module_sizes':{leaf:{'file':paths[leaf],'lines':len(src.splitlines()),'max_width':max(map(len,src.splitlines()),default=0),
  'sha256':sha(src.encode())} for leaf,src in texts.items()},'proposed_imports':plan['proposed_imports'],
 'header_prose_guard_inputs':{'frozen_global_map_sha256':sha((W/'evidence/checks/m3-final-v2/global-freeze/frozen-global-map.json').read_bytes()),
 'current_global_map_sha256':sha((W/'evidence/checks/m3-final-v2/global-freeze/current-global-map.json').read_bytes())},
 'generated_constants':'Named lexical census only. Exact structure commands stay unchanged; generated fields/recursors and full kernel types require root checks.',
 'Lean_Git_cache_source_agents':False}
assert summary['template_sorry_count']==4
(B/'template-validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print('42 exact M0 declaration moves;38 Defs/3 Encoding/1 Hop;Transport empty;4 original stubs unchanged')
print(json.dumps(summary['module_sizes'],indent=2))
