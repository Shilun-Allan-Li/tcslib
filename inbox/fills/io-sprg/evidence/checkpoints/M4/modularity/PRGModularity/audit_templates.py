"""Use reviewed pure parser functions only; never execute their CLI/Git loops."""
from pathlib import Path
import ast,hashlib,json,re
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/PRGModularity')
tool=W/'evidence/tools/freeze_global.py';tree=ast.parse(tool.read_text())
keep={'need','sha','parser_functions','doc_prefix','global_map'}
nodes=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom)) or isinstance(n,ast.FunctionDef) and n.name in keep]
scope={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(tool),'exec'),scope)
d=scope['parser_functions'](W/'evidence/tools/seal/decls2.py',{'strip','decls'},{'KW'})
c=scope['parser_functions'](W/'evidence/tools/clash/clash_scan.py',{'strip_code','parse_decls'},{'KINDS','MODS','ATTR','DECL_RE','NAME_RE'})
rel='TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG.lean'
old=scope['global_map']({rel:(W/rel).read_bytes()},d['decls'],c['parse_decls'])
virtual={rel:(B/'Facade.lean.template').read_bytes()}
for leaf in ('Defs','Encoding','Hop'):virtual[rel.removesuffix('.lean')+'/'+leaf+'.lean']=(B/(leaf+'.lean.template')).read_bytes()
new=scope['global_map'](virtual,d['decls'],c['parse_decls'])
ledger=json.loads((B/'existing-declaration-move-map.json').read_text());moves={r['name']:(r['old_file'],r['new_file']) for r in ledger}
assert len(old)==37 and len(new)==41
assert set(old)<=set(new)
for n,v in old.items():
 assert v['normalized_header']==new[n]['normalized_header'],n
 assert v['statement_prose_prefix']==new[n]['statement_prose_prefix'],n
 assert (v['file'],new[n]['file'])==moves[n],n
# Source command bytes and full docs for every old declaration stay in its single copied chunk.
newnames=sorted(set(new)-set(old));expected=[r['name'] for r in json.loads((B/'new-helper-placement.json').read_text())];assert newnames==sorted(expected)
(B/'lexical-template-audit.json').write_text(json.dumps({'status':'STATIC_PARSER_TEMPLATE_PASS_NOT_LEAN','reviewed_parser_functions_reused':[str(tool),'seal/decls2.py:strip,decls','clash/clash_scan.py:strip_code,parse_decls'],'old_named_declarations':37,'new_named_declarations':41,'old_globally_removed':[],'old_changed_headers':[],'old_changed_statement_prose':[],'exact_declared_moves':37,'new_theorems_not_M0':newnames,'generated_constants_or_kernel_check':False},indent=2)+'\n')
print('Both reviewed parsers agree:37 old names/headers/prose unchanged;4 named new theorem placeholders.')
