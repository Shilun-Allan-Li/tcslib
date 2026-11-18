"""Read-only split planning: metadata and tactic-free headers only. Never invokes Lean."""
from pathlib import Path
import csv,hashlib,json,re
base=Path('/private/tmp/io-sprg-proof-notes/LPNModularity')
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
rel=Path('TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN.lean')
src=(repo/rel).read_text();lines=src.splitlines()
prefix='TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN'
blocks=[{'target':prefix+'.Defs','ranges':[[49,361],[408,424]],
 'new_candidates':[],'role':'Every existing definition/abbrev/instance plus adjacent readers; LPNRealizable moves with its reader.'},
 {'target':prefix+'.Encoding','ranges':[[363,386]],'new_candidates':[],
 'role':'Existing lpnEnc_injective, encLPNAdvice_injective, encLPNAdvice_length_le with frozen headers.'},
 {'target':prefix+'.Transport','ranges':[],
 'new_candidates':['01','02','03','04'],'role':'Specialized coin/verdict and canonical challenge-coordinate transports, all in area Internal.'},
 {'target':prefix+'.Hop','ranges':[[388,406]],
 'new_candidates':['05','06','07','08','09','10'],
 'role':'Pointwise preprocessing, fixed-advice sections, actual-law averaging, then unchanged public Params.lpn_hop header.'}]
imports={prefix:[prefix+'.Defs',prefix+'.Encoding',prefix+'.Transport',prefix+'.Hop'],
 prefix+'.Defs':['TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids',
                'TCSlib.Cryptography.Asymptotic.Realization'],
 prefix+'.Encoding':[prefix+'.Defs','TCSlib.Cryptography.Obfuscation.StructuredSeed.Basic'],
 prefix+'.Transport':[prefix+'.Defs'],prefix+'.Hop':[prefix+'.Transport']}
(base/'move-boundaries.json').write_text(json.dumps({'source':str(repo/rel),
 'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'source_lines':len(lines),
 'facade':prefix,'blocks':blocks,'proposed_imports':imports},indent=2)+'\n')
starts=[]
for i,l in enumerate(lines):
 m=re.match(r'^(?:noncomputable\s+)?(abbrev|def|structure|instance|theorem)\s+([^\s(:]+)',l)
 if m:starts.append((i,m[1],m[2]))
records=[]
for ix,(i,kind,name)in enumerate(starts):
 end=starts[ix+1][0]if ix+1<len(starts)else 425
 docs=[j for j in range(i+1,end)if lines[j].startswith('/--')]
 if docs:end=docs[0]
 command='\n'.join(lines[i:end]).rstrip()+'\n'
 mark=command.find(':=');where=re.search(r'\bwhere\b',command)
 if where and(mark<0 or where.start()<mark):mark=where.start()
 if mark<0:raise RuntimeError(name)
 header=command[:mark].rstrip()
 target=prefix+'.Defs'
 if name in('lpnEnc_injective','encLPNAdvice_injective','encLPNAdvice_length_le'):target=prefix+'.Encoding'
 if name=='lpn_hop':target=prefix+'.Hop'
 records.append({'name':'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.'+name,
  'kind':kind,'old_start':i+1,'old_end':end,'target_module':target,
  'header_sha256':hashlib.sha256(header.encode()).hexdigest(),
  'command_sha256':hashlib.sha256(command.encode()).hexdigest(),
  'frozen_command_must_move_verbatim':target==prefix+'.Defs'})
assert len(records)==42
(base/'declarations.json').write_text(json.dumps(records,indent=2)+'\n')
with(base/'declarations.tsv').open('w')as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['fullname','kind','old_start','old_end','target_module','header_sha256','command_sha256'])
 for r in records:w.writerow([r[k]for k in('name','kind','old_start','old_end','target_module','header_sha256','command_sha256')])

copyright='''/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
'''
options='''
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
'''
reference='''
## References

* [JLS26] Jain, Lin, Sahai, J. ACM 73(1), Article 1, February 2026,
  Lemma 4.2, p. 19.
* [PS10] Pass, Shelat, *A Course in Cryptography*, 2010, Definition 26.8.
'''
notes={
 'Defs':('LPN reduction data and exact readers',[
 '* Canonical challenge/encoding and explicit finite casts.',
 '* Inhabited sentinel advice, encoders and deterministic reduction.',
 '* `Params.LPNRealizable` and its complete contract reader.'],
 'Dv3, Dv9, Dv12 and Dv15 preserve the exact challenge, advice layout and casts;\nDv14 and Dv16 keep function-level reductions and the shared realization contract.'),
 'Encoding':('Injective and polynomially bounded LPN reduction encodings',[
 '* Canonical challenge-code injectivity.',
 '* Advice-code injectivity and its explicit polynomial bound.'],
 'Dv9, Dv12 and Dv15 retain the prime-first fixed-layout advice code;\nno encoder, algorithm, sampler or polynomial-bound definition changes.'),
 'Transport':('Canonical LPN coordinates and shared realizer transport',[
 '* `Internal.lpn_accept_realizes_eq` and `lpn_gap_realizes_eq`.',
 '* Uniform challenge and real sample-seed coordinate bridges.'],
 'Dv3 and Dv15 transport the existing canonical challenge and exact law.\nDv16 uses shared layout-only verdict and coin readers; no new machine is built.'),
 'Hop':('Actual-law LPN averaging and the selected hybrid hop',[
 '* Pointwise preprocessing identities and fixed-advice section acceptances.',
 '* Actual-nuisance-law advice fixing before every realizer.',
 '* `Params.lpn_hop` with its unchanged full statement.'],
 'Dv8 and Dv12 retain the actual independent nuisance law and global advice family.\nDv16 quantifies every realizer of the same layout-only explicit reduction.')}
headers={};footers={}
for leaf,(title,bullets,deviation)in notes.items():
 ns='Params'if leaf in('Defs','Encoding')else'Internal'
 text=copyright+''.join('import '+x+'\n'for x in imports[prefix+'.'+leaf])+options
 text+='\n/-!\n# '+title+'\n\n## Main definitions and results\n\n'+'\n'.join(bullets)+'\n'+reference
 text+='\n**Deviations.** '+deviation+'\n-/\n\n'
 text+='namespace TCSlib.Cryptography.Obfuscation.StructuredSeed\n\n'
 text+='open Complexity Turing\nopen scoped BigOperators\n\nnamespace '+ns+'\n\n'
 headers[leaf]=text
 footers[leaf]='\nend '+ns+'\n\nend TCSlib.Cryptography.Obfuscation.StructuredSeed\n'
 (base/(leaf+'.header.lean.txt')).write_text(text+'-- MOVE THE RECORDED COMMAND BLOCKS HERE; NO NEW DEFINITIONS.\n'+footers[leaf])
facade=copyright+''.join('import '+x+'\n'for x in imports[prefix])+options
facade+='''
/-!
# The explicit advice-based LPN reduction

## Contents

* `Defs`: canonical challenge, advice, exact reduction definitions and readers.
* `Encoding`: canonical/advice injectivity and polynomial advice bound.
* `Transport`: canonical coordinate laws and shared realizer transport.
* `Hop`: fixed-advice sections, actual-law averaging, and the selected hop theorem.
'''+reference+'''
**Deviations.** Dv3, Dv8, Dv9, Dv12, Dv14, Dv15 and Dv16 are retained in the
owning child docstrings. All existing public full names and statements are preserved.
-/
'''
(base/'Facade.header.lean.txt').write_text(facade)
# Compute sizes in memory only; do not write multiple proof blocks or split source modules.
p=Path('/private/tmp/io-sprg-proof-notes/LPNHopFinal')
candidates={int(f.name[:2]):f.read_text()for f in p.iterdir()if f.suffix in('.candidate','.proof')}
oldenc=Path('/private/tmp/io-sprg-proof-notes/LPNHop')
def linecount(s):return len(s.splitlines())
def chunk(a,b):return '\n'.join(lines[a-1:b])+'\n'
vals={}
vals['Defs']=linecount(headers['Defs']+chunk(49,361)+'\n'+chunk(408,424)+footers['Defs'])
enc=chunk(363,386)
for filename in('01-lpnEnc_injective.lean.txt','02-encLPNAdvice_injective.PARTIAL.lean.txt',
 '03-encLPNAdvice_length_le.PARTIAL.lean.txt'):
 enc=enc.replace('sorry',(oldenc/filename).read_text(),1)
vals['Encoding_current_PARTIAL']=linecount(headers['Encoding']+enc+footers['Encoding'])
vals['Transport_current_NOT_RUN']=linecount(headers['Transport']+'\n'.join(candidates[i]for i in range(1,5))+footers['Transport'])
hop=chunk(388,406).replace('sorry',candidates[10],1)
vals['Hop_current_NOT_RUN']=linecount(headers['Hop']+'\n'.join(candidates[i]for i in range(5,10))+
 '\nend Internal\n\nnamespace Params\n\n'+hop+
 '\nend Params\n\nend TCSlib.Cryptography.Obfuscation.StructuredSeed\n')
vals['Facade']=linecount(facade)
vals['packet_total_01_to_10']=sum(linecount(v)for v in candidates.values())
vals['unsplit_plus_old_partial_encoding']=len(lines)+sum(linecount(candidates[i])for i in range(1,10))+linecount(candidates[10])-1+sum(linecount((oldenc/f).read_text())-1 for f in('01-lpnEnc_injective.lean.txt','02-encLPNAdvice_injective.PARTIAL.lean.txt','03-encLPNAdvice_length_le.PARTIAL.lean.txt'))
(base/'line-budget.json').write_text(json.dumps({'status':'STATIC_ESTIMATE_NOT_PROOF',
 'exact_text_counts':vals,'known_local_have_extra_lines':{'Transport':3,'Hop':5},
 'recommended_final_budgets':{'Defs':'about 380, unchanged commands',
 'Encoding':'300-500; existing two partial advice bodies need completion',
 'Transport':'220-400; narrow real-seed cast proof may grow',
 'Hop':'400-600; typed actual-law averaging may grow',
 'Facade':'about 40'},
 'fallback':'If Hop approaches 550 before completion, move candidate05-08 intact to LPN/Sections, import Transport there, and make Hop import Sections.'},indent=2)+'\n')
print('42 declaration moves fingerprinted; tactic-free header plans and exact text line budget written.')
print(json.dumps(vals))
