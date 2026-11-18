"""Temp-only install_helper schema/spec verification. Does not execute installer."""
from pathlib import Path
import ast
import csv
import hashlib
import io
import json
import re
import textwrap

W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/M4PRGHelperSpecs')
PRE=Path('/private/tmp/io-sprg-proof-notes/M4PRGPrepared')
TEMPLATE=Path('/private/tmp/io-sprg-proof-notes/PRGModularity/Hop.lean.template')
AREA='TCSlib/Cryptography/Obfuscation/StructuredSeed/'
PREFIX='TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.'
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
raw=TEMPLATE.read_text()
H0='\n/-- H0-H3 sample the actual index and seed law and alter only error flag and output\n'
HOP='\nnamespace Params\n'
entries=[
 ('sdCore_publicSeed',B/'candidates/01-sdCore_publicSeed.in-Params.proposed.lean','Hybrids.lean',H0,'sdCore_publicSeed_core',
  ['TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_seed',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_instances',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_err',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.packSeed_fst',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.publicSeed_eq'],[],
  'COMPONENT_CORE_ACTUAL_READERS_ABSTRACTED; source sdCore/pack/publicSeed identities are the separate exact body',
  'Only Params.sdCore_publicSeed declaration token becomes bare sdCore_publicSeed inside existing Params; body/types/doc unchanged.'),
 ('Params.prg_verdict_prob',PRE/'preferred-MRr3/04-prg_verdict_prob.proposed.lean','Reductions/PRG/Hop.lean',HOP,'prg_verdict_prob_core',
  ['Complexity.NUPPT.distinguisherL_eq','Complexity.NUPPT.RealizesOn.runAt_coinsEquivPoly_symm',
   'Complexity.NUPPT.RealizesOn.coins_eq','TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgRed_eq',
   'TCSlib.Cryptography.HardcoreBit.pushesUniform_restrict'],[],
  'COMPONENT_CORE_ACTUAL_READERS_ABSTRACTED; MRr3 bitvector activation reader and actual coin restriction remain explicit in candidate',
  'Preferred MRr3 helper04; keeps qualified Params header before source namespace Params.'),
 ('Params.prg_nuisance_average',PRE/'candidates/PRGHopFinal/05-prg_nuisance_average.typed.proposed.lean','Reductions/PRG/Hop.lean',HOP,'prg_nuisance_average_core',
  ['TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idSamp\'_eq',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.idCore_eq',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG.idSamp_eq',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.PRGAdvice.prodEquiv',
   'TCSlib.Cryptography.Games.ProbComp.expect_sample_equiv','TCSlib.Cryptography.Games.Bridge.expect_sample_pair'],[],
  'COMPONENT_CORE_ACTUAL_READERS_ABSTRACTED; actual generator index law remains the idCore pushforward, not a uniform G.Idx draw',
  'Preferred explicitly typed helper05; keeps qualified Params header before source namespace Params.'),
 ('Params.prg_chain_accept_average',PRE/'candidates/PRGHopFinal/06-prg_chain_accept_average.proposed.lean','Reductions/PRG/Hop.lean',HOP,'prg_chain_output_reindex_core',
  ['TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prg_nuisance_average',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.chainGame_eq',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.prgPre_eq',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.kappaOfN_n',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.m_eq',
   'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.outputIndex_eq'],
  [PREFIX+'prg_nuisance_average'],
  'OUTPUT_REINDEX_COMPONENT_CORE; complete image/chain/preprocessing normalization plus nuisance averaging remain source obligations',
  'Helper06 retains qualified Params header; install after helper05, before original prg_hop namespace block.')
]
rows=[];dry={};metadata=[]
for order,(name,path,leaf,marker,core,deps,helperdeps,scope,note) in enumerate(entries,1):
 full=PREFIX+name.split('.')[-1];qualified='Params.'+name.split('.')[-1]
 m=re.search(r'^theorem '+re.escape(qualified)+r'(?=\s|\(|\{|:)',raw,re.M);assert m
 ds=raw.rfind('/--',0,m.start());de=raw.find('-/',ds)+2
 assert not raw[de:m.start()].strip()
 docraw=raw[ds:de];doctext=docraw[3:-2].strip()
 token=raw.index(':= __PRG_HELPER_',m.start())
 original_header=raw[m.start():token].rstrip()
 candidate=path.read_text();start=re.search(r'^theorem '+re.escape(name)+r'(?=\s|\(|\{|:)',candidate,re.M);assert start
 tail=candidate[start.start():];by=re.search(r':=\s+by\n',tail);assert by
 header=tail[:by.start()].rstrip();body='by\n'+tail[by.end():].rstrip()+'\n'
 assert candidate[:start.start()].strip()==docraw,'candidate doc differs from original Hop template'
 expected=original_header.replace('theorem '+qualified,'theorem '+name,1)
 assert header==expected,'candidate type/header drift'
 assert body.count('by\n')==1 and not re.search(r'\b(sorry|admit)\b',body)
 owner=AREA+leaf;source=(W/owner).read_text();assert source.count(marker)==1
 assert not re.search(r'^theorem '+re.escape(name)+r'\b',source,re.M)
 rendered='\n\n'.join(textwrap.fill(p,width=92) for p in doctext.split('\n\n'))
 stub='\n/-- '+rendered+' -/\n'+header+' := sorry\n'
 if owner not in dry:dry[owner]=source
 dry[owner]=dry[owner].replace(marker,stub+marker)
 probe='M4PRG_'+core
 row={'name':name,'file':owner,'candidate':str(path),'marker':marker,'probe':probe,'doc':doctext,
  'full_name':full,'install_order':order,'header':header,
  'candidate_sha256':sha(candidate),'header_sha256':sha(header),'body_sha256':sha(body),
  'original_qualified_header_sha256':sha(original_header),'original_template_docstring_sha256':sha(docraw),
  'doc_text_sha256':sha(doctext),'installer_rendered_docstring_sha256':sha('/-- '+rendered+' -/'),
  'original_template':str(TEMPLATE),'original_template_sha256':sha(raw),
  'owner_source_sha256_at_preparation':sha(source),'owner_marker_occurrences':1,
  'dependencies':deps,'new_helper_dependencies':helperdeps,'overlap_core_name':core,
  'overlap_scope':scope,'overlap_record_exists_at_preparation':(W/'evidence/overlap/probes'/probe/'search.json').exists(),
  'placement_note':note,'status':'UNRUN_NOT_INSTALLED_NO_LEAN'}
 rows.append(row)
# Reuse only the pure declaration parser to dry-run final names/namespace scopes in memory.
p=W/'evidence/tools/clash/clash_scan.py';tree=ast.parse(p.read_text());nodes=[]
constants={'KINDS','MODS','ATTR','DECL_RE','NAME_RE'}
for n in tree.body:
 if isinstance(n,(ast.Import,ast.ImportFrom)):nodes.append(n)
 elif isinstance(n,ast.FunctionDef) and n.name in {'strip_code','parse_decls'}:nodes.append(n)
 elif isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in constants for t in n.targets):nodes.append(n)
parser={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(p),'exec'),parser)
for row in rows:
 names=[d['full'] for d in parser['parse_decls'](dry[row['file']])]
 assert names.count(row['full_name'])==1,'wrong actual full name after namespace insertion'
 # Equality of canonical name plus unchanged literal binder/result header proves
 # the leaf-token adjustment does not create Params.Params or change its type.
 assert row['header'].replace('theorem '+row['name'],'theorem '+row['full_name'],1)==\
  raw[raw.index('theorem Params.'+row['name'].split('.')[-1]):raw.index(':= __PRG_HELPER_',raw.index('theorem Params.'+row['name'].split('.')[-1]))].rstrip().replace('theorem Params.'+row['name'].split('.')[-1],'theorem '+row['full_name'],1)
(B/'M4-PRG-helper-specs.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
fields=['install_order','name','full_name','file','probe','candidate_sha256','header_sha256','body_sha256','original_template_docstring_sha256','status']
buf=io.StringIO();wr=csv.DictWriter(buf,fieldnames=fields,delimiter='\t',lineterminator='\n');wr.writeheader();wr.writerows({k:r[k] for k in fields} for r in rows)
(B/'helper-specs-index.tsv').write_text(buf.getvalue())
(B/'validation.json').write_text(json.dumps({'status':'STATIC_INSTALLER_SCHEMA_DRY_RUN_ONLY_NOT_EXECUTED',
 'installer':'evidence/tools/install_helper.py','installer_source_sha256':sha((W/'evidence/tools/install_helper.py').read_text()),
 'rows':4,'actual_full_names_verified':[r['full_name'] for r in rows],
 'original_template_docstrings_unchanged':True,'doc_rendering':'Installer rewraps paragraphs at92; exact input and rendered hashes separately recorded',
 'candidate_variant_choices':['bare-leaf01 inside Params','preferred-MRr3-04','typed05','prepared06'],
 'owner_markers_unique':True,'source_stub_simulation':'Memory only; no implementation or stub files written',
 'source_candidate_body_changes':'Only01 name token; zero body changes to any candidate',
 'Lean_Git_cache_agents_source_installer_execution':False},indent=2)+'\n')
print('Four root-compatible helper specs; exact template docs/header/body hashes; full FQNs dry-run verified')
