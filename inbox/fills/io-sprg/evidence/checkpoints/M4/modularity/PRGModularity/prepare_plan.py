"""Read-only PRG split metadata and tactic-free source templates. Never invokes Lean or Git."""
from pathlib import Path
import ast,csv,hashlib,io,json,re
B=Path('/private/tmp/io-sprg-proof-notes/PRGModularity')
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
rel='TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG.lean'
source=(W/rel).read_text();lines=source.splitlines();owner='TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG'
basepath='TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/'
freeze_path=W/'evidence/checks/m3-final/global-freeze/frozen-global-map.json'
current_path=W/'evidence/checks/m3-final/global-freeze/current-global-map.json'
freeze=json.loads(freeze_path.read_text());current=json.loads(current_path.read_text())
summary=json.loads((current_path.parent/'summary.json').read_text())
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
assert summary['current_source_sha256'][rel]==sha(source)
old={n:v for n,v in freeze.items() if v['file']==rel};assert len(old)==37
imports={owner:[owner+'.Defs',owner+'.Encoding',owner+'.Hop'],owner+'.Defs':['TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids','TCSlib.Cryptography.Asymptotic.Realization'],owner+'.Encoding':[owner+'.Defs'],owner+'.Hop':[owner+'.Defs']}
ranges={'Defs':[[51,297]],'Encoding':[[299,324]],'Hop':[[326,343]]}
enc_names={'prgEnc_injective','encPRGAdvice_injective','encPRGAdvice_length_le'}
ledger=[]
starts=sorted(current[n]['line'] for n in old)
for name,v in old.items():
 now=current[name];assert now['header_sha256']==v['header_sha256'] and now['prose_prefix_sha256']==v['prose_prefix_sha256']
 leaf='Encoding' if name.rsplit('.',1)[-1] in enc_names else 'Hop' if name.endswith('.prg_hop') else 'Defs'
 start=now['line'];j=start-2
 while j>=0 and not lines[j].strip():j-=1
 doc='';docstart=None
 if j>=0 and lines[j].rstrip().endswith('-/'):
  k=j
  while k>=0 and '/--' not in lines[k]:k-=1
  if k>=0:doc='\n'.join(lines[k:j+1])+'\n';docstart=k+1
 stop=min([q-1 for q in starts if q>start]+[344])
 for q in range(start,stop):
  if lines[q].startswith(('/--','namespace ','end ')):
   stop=q;break
 command='\n'.join(lines[start-1:stop]).rstrip()+'\n'
 ledger.append({'name':name,'old_file':rel,'new_file':basepath+leaf+'.lean','kind':v['kind'],'old_start':start,'old_doc_start':docstart,'old_end':stop,'target_module':owner+'.'+leaf,'frozen_header_sha256':v['header_sha256'],'current_header_sha256':now['header_sha256'],'frozen_statement_prose_sha256':v['prose_prefix_sha256'],'current_statement_prose_sha256':now['prose_prefix_sha256'],'full_docstring_sha256':sha(doc),'command_sha256':sha(command),'definition_or_reader_moves_verbatim':leaf=='Defs'})
assert sum(r['definition_or_reader_moves_verbatim'] for r in ledger)==33
(B/'existing-declaration-move-map.json').write_text(json.dumps(ledger,indent=2)+'\n')
stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=list(ledger[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(ledger);(B/'existing-declaration-move-map.tsv').write_text(stream.getvalue())
metadata={'status':'READ_ONLY_PROPOSED_MOVE_NOT_IMPLEMENTED','source':str(W/rel),'source_sha256':sha(source),'source_lines':len(lines),'facade':owner,'old_public_named_declarations':37,'old_definitions_instances_readers_moving_verbatim':33,'blocks':[{'target':owner+'.'+k,'ranges':r} for k,r in ranges.items()],'proposed_imports':imports,'global_M0_freeze':summary['freeze'],'global_M0_ledger':str(freeze_path),'global_current_ledger':str(current_path),'global_freeze_evidence_capture':summary['HEAD_at_capture'],'all37_match_frozen_headers_and_statement_prose':True,'generated_constants_qualification':'Named lexical ledger only; generated fields/recursors and final kernel census are not newly checked.'}
(B/'move-boundaries.json').write_text(json.dumps(metadata,indent=2)+'\n')
copyright='''/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
'''
options='''
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
'''
refs='''
## References

* [JLS26] Jain, Lin, Sahai, J. ACM 73(1), Article 1, February 2026,
  Lemma 4.2, p. 19; Definition 3.4, p. 11.
* [PS10] Pass, Shelat, A Course in Cryptography, 2010, Definition 26.8.
'''
notes={'Defs':('Boolean PRG reduction data and exact readers','Canonical challenge; inhabited explicit finite advice; prime-first encoding;\ndeterministic preprocessing and reduction; shared realization obligation.','Dv4, Dv8, Dv9, Dv12, Dv14, Dv15 and Dv16 retain the existing challenge,\nprime-first advice, finite coordinates and layout-length realization contract.'),'Encoding':('Injective and bounded Boolean PRG reduction encodings','The three original canonical/advice injectivity and advice-length theorems.','Dv9, Dv12 and Dv15 count the unchanged prime-first advice layout and\nall explicit hardwired fields, with no new encoder or sampler.'),'Hop':('Actual-law Boolean PRG averaging and the final hybrid hop','The four specialized sampler/verdict/averaging helper theorems and\nthe original every-realizer Params.prg_hop conclusion.','Dv8 and Dv12 preserve the actual nuisance law and fix advice before\nevery realizer. Dv16 uses only the shared layout-length realization contract.')}
def header(leaf):
 title,contents,dev=notes[leaf]
 return copyright+''.join('import '+m+'\n' for m in imports[owner+'.'+leaf])+options+'\n/-!\n# '+title+'\n\n## Main definitions and results\n\n'+contents+'\n'+refs+'\n**Deviations.** '+dev+'\n-/\n\nnamespace TCSlib.Cryptography.Obfuscation.StructuredSeed\n\nopen Complexity Turing Games\n\n'
def chunk(a,b):return '\n'.join(lines[a-1:b])+'\n'
footer='\nend Params\n\nend TCSlib.Cryptography.Obfuscation.StructuredSeed\n'
texts={}
for leaf in ('Defs','Encoding'):
 texts[leaf]=header(leaf)+'namespace Params\n\n'+''.join(chunk(a,b) for a,b in ranges[leaf])+footer
 (B/(leaf+'.lean.template')).write_text(texts[leaf])
R=Path('/private/tmp/io-sprg-proof-notes/M4PRGPrepared/candidates/PRGHopFinal')
helperpaths=[R/'01-sdCore_publicSeed.proposed.lean',R/'04-prg_verdict_prob.proposed.lean',R/'05-prg_nuisance_average.typed.proposed.lean',R/'06-prg_chain_accept_average.proposed.lean']
helpermap=[];helperheaders=[]
for p in helperpaths:
 s=p.read_text();assert ':= by' in s
 h=s.split(':= by',1)[0].rstrip();token='__PRG_HELPER_'+p.name[:2]+'__'
 helperheaders.append(h+' := '+token+'\n');m=re.search(r'(?m)^theorem\s+(\S+)',h)
 helpermap.append({'name':'TCSlib.Cryptography.Obfuscation.StructuredSeed.'+m[1],'target_module':owner+'.Hop','candidate':str(p),'candidate_sha256':sha(s),'header_sha256':sha(h),'template_token':token,'status':'NEW_THEOREM_CANDIDATE_NOT_FROZEN_NOT_RUN'})
texts['Hop']=header('Hop')+'\n'.join(helperheaders)+'\nnamespace Params\n\n'+chunk(326,343)+footer
(B/'Hop.lean.template').write_text(texts['Hop']);(B/'new-helper-placement.json').write_text(json.dumps(helpermap,indent=2)+'\n')
facade=copyright+''.join('import '+m+'\n' for m in imports[owner])+options+'''
/-!
# The explicit advice-taking JLS Boolean PRG reduction

## Contents

* `Defs`: canonical challenge, finite advice, encoders, preprocessing and readers.
* `Encoding`: the original three injection and polynomial advice-bound theorems.
* `Hop`: actual-law sampler/verdict/averaging glue and the final PRG hop.
'''+refs+'''
Dv4, Dv8, Dv9, Dv12, Dv14, Dv15 and Dv16 remain documented in the owning children.
Every old public full name, header, definition and statement docstring is retained.
-/
'''
(B/'Facade.lean.template').write_text(facade)
# Assemble only in memory for a static size estimate; no multi-proof file is written.
A=Path('/private/tmp/io-sprg-proof-notes/M4AdviceEncoding')
enc=texts['Encoding']
for p in sorted(A.glob('0[4-6]*.proof')):enc=enc.replace('sorry',p.read_text().rstrip(),1)
hop=texts['Hop']
for r,p in zip(helpermap,helperpaths):hop=hop.replace(r['template_token'],'by'+p.read_text().split(':= by',1)[1],1)
hop=hop.replace('sorry',(R/'07-prg_hop.proof').read_text().rstrip(),1)
counts={'Defs':len(texts['Defs'].splitlines()),'Encoding_with_full_UNRUN_bodies':len(enc.splitlines()),'Hop_with_full_UNRUN_bodies':len(hop.splitlines()),'Facade':len(facade.splitlines())}
(B/'line-budget.json').write_text(json.dumps({'status':'TEXT_ONLY_NOT_IMPLEMENTED_NOT_CHECKED','known_assembled_lines':counts,'target_range':'150-600 lines per substantive implementation child','headroom_before600':{k:600-v for k,v in counts.items() if k!='Facade'},'note':'Old declaration docs move verbatim. New helper docs are already included. Elaboration-driven growth unknown.'},indent=2)+'\n')
for leaf,text in texts.items():
 assert len(re.findall(r'\bby\b',re.sub(r'/-[\s\S]*?-/', '',text)))==0,leaf
 assert max(map(len,text.splitlines()))<=100,leaf
for leaf,rs in ranges.items():
 for a,b in rs:assert chunk(a,b) in texts[leaf]
print('37 exact M0 moves:33 Defs,3 Encoding,1 Hop. Tactic-free templates staged.',counts)
