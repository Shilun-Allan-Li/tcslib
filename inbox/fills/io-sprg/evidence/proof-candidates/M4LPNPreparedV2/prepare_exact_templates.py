from pathlib import Path
import hashlib,json,re,shutil
B=Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared');T=B/'overlap/exact-statements';T.mkdir(parents=True,exist_ok=True)
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
owner='TCSlib.Cryptography.Obfuscation.StructuredSeed';Defs=owner+'.Reductions.LPN.Defs'
indices=[]
for p in sorted(B.glob('*.lean.candidate')):
 s=p.read_text();start=re.search(r'(?m)^theorem\s+(\S+)',s);assert start
 header=s[start.start():].split(':= by',1)[0].rstrip();leaf=start[1]
 old=Path('/private/tmp/io-sprg-proof-notes/LPNHopFinal')/p.name;o=old.read_text();oh=o[re.search(r'(?m)^theorem ',o).start():].split(':= by',1)[0].rstrip()
 assert ' '.join(header.split())==' '.join(oh.split()),p.name
 full=owner+'.Internal.'+leaf
 example=re.sub(r'^theorem\s+\S+','example',header,count=1)
 text='import '+Defs+'\nimport Lean.Elab.Tactic.LibrarySearch\n\nset_option maxHeartbeats 100000\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n\nnamespace '+owner+'\n\nopen Complexity Turing Games\n'
 if '∑' in header or '∏' in header:text+='open scoped BigOperators\n'
 text+='\nnamespace Internal\n\n'+example+'\n  := __PROBE_BODY__\n\nend Internal\n\nend '+owner+'\n'
 target=T/(p.name[:2]+'-'+leaf+'.lean.template');target.write_text(text)
 (B/(p.name[:2]+'-'+leaf+'.statement.txt')).write_text(header+'\n')
 indices.append({'index':int(p.name[:2]),'name':full,'original_or_new':'PROPOSED_NEW_HELPER','placement':owner+'.Reductions.LPN.'+('Transport' if int(p.name[:2])<=4 else 'Sections' if int(p.name[:2])<=8 else 'Hop'),'candidate':str(p),'candidate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'header_sha256':hashlib.sha256(header.encode()).hexdigest(),'header_unchanged_from_LPNHopFinal':True,'template':str(target),'template_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'exact_status':'NOT_RUN','apply_status':'NOT_RUN','project_imports':[Defs],'whole_goal_assumptions':'Exactly actual theorem premises, no added goal hypothesis.'})
hop=W/'TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Hop.lean';s=hop.read_text();m=re.search(r'(?m)^theorem lpn_hop\b[\s\S]*? := sorry',s);assert m
header=m[0].removesuffix(' := sorry');example=header.replace('theorem lpn_hop','example',1)
text='import '+Defs+'\nimport Lean.Elab.Tactic.LibrarySearch\n\nset_option maxHeartbeats 100000\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n\nnamespace '+owner+'\n\nopen Complexity Turing Games\n\nnamespace Params\n\n'+example+'\n  := __PROBE_BODY__\n\nend Params\n\nend '+owner+'\n'
target=T/'10-lpn_hop.lean.template';target.write_text(text);p=B/'10-lpn_hop.proof';(B/'10-lpn_hop.statement.txt').write_text(header+'\n')
indices.append({'index':10,'name':owner+'.Params.lpn_hop','original_or_new':'FROZEN_M0_ORIGINAL','placement':owner+'.Reductions.LPN.Hop','candidate':str(p),'candidate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'header_sha256':hashlib.sha256(header.encode()).hexdigest(),'source':str(hop),'source_sha256':hashlib.sha256(hop.read_bytes()).hexdigest(),'template':str(target),'template_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'exact_status':'NOT_RUN','apply_status':'NOT_RUN','project_imports':[Defs],'whole_goal_assumptions':'Exactly frozen original premises.'})
assert len(indices)==10
(B/'overlap/exact-probe-index.json').write_text(json.dumps(indices,indent=2)+'\n')
P=B/'overlap/public-cores';P.mkdir(exist_ok=True)
cores=[]
for src in sorted(Path('/private/tmp/io-sprg-proof-notes/M4LPN09Review/overlap/templates').glob('*.template')):
 dest=P/src.name;shutil.copyfile(src,dest);cores.append({'template':str(dest),'sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'source':str(src),'purpose':'Public product/matrix-commutation/coordinate-resampling composition diagnostics, not proposed generic source helpers.','exact_status':'NOT_RUN','apply_status':'NOT_RUN'})
(B/'overlap/public-core-index.json').write_text(json.dumps(cores,indent=2)+'\n')
print('Ten EXACT-STATEMENT Defs-only templates; all nine helper headers unchanged; three public-only composition cores retained.')
