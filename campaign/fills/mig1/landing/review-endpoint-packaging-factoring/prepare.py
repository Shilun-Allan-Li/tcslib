"""Build inert proof-only Catalog proposals and tightly scoped guard copies."""
from pathlib import Path
import difflib, hashlib, json, re, sys

p=Path(__file__).resolve().parent;root=p.parents[4]
chunk_code=(root/'devtools/seyoon/declfreeze.py').read_text()
ns={};exec(compile(chunk_code.split('a = chunks(')[0],'<reviewed-declaration-chunks>','exec'),ns)
chunks=ns['chunks']

def assignment(s):
 stack=[];comment=0;string=False;i=0;pairs={')':'(',']':'[','}':'{','⟩':'⟨'}
 while i<len(s):
  if comment:
   if s.startswith('/-',i):comment+=1;i+=2;continue
   if s.startswith('-/',i):comment-=1;i+=2;continue
   i+=1;continue
  if string:
   if s[i]=='\\':i+=2;continue
   if s[i]=='"':string=False
   i+=1;continue
  if s.startswith('/-',i):comment=1;i+=2;continue
  if s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j+1;continue
  c=s[i]
  if c=='"':string=True;i+=1;continue
  if c in '([{⟨':stack.append(c)
  elif c in pairs:assert stack and stack.pop()==pairs[c]
  elif not stack and s.startswith(':=',i):return i
  i+=1
 return None

def repoint(source,name):
 rows={n:t for n,_,t in chunks(source)};old=rows[name];pos=assignment(old)
 assert pos is not None
 old_body=old[pos+2:]
 a=old_body.index('  ·\n    funext j p\n')+len('  ·\n    funext j p\n')
 b=old_body.index('\n  · funext j\n',a)
 cell=old_body[a:b]
 assert all(not line or line.startswith('  ') for line in cell.splitlines())
 cell='\n'.join(line[2:] if line else line for line in cell.splitlines())
 new=old[:pos+2]+' by\n  apply catalog_ofWords_with_tapes\n  intro j p\n'+cell
 assert source.count(old)==1
 return source.replace(old,new,1)

version=sys.argv[1]
assert version in ['v1','v2']
before=(p/'Catalog-before.lean.txt').read_text()
helper=(p/'helper.lean.txt').read_text().rstrip()
transfer='Turing.Cfg.ofWords_transfer_endpoint';copy='Turing.Cfg.ofWords_copy_endpoint'
old_transfer={n:t for n,_,t in chunks(before)}[transfer]
assert before.count(old_transfer)==1
proposal=before.replace(old_transfer,helper+'\n\n'+old_transfer,1)
proposal=repoint(proposal,transfer)
if version=='v2':proposal=repoint(proposal,copy)
destination=p/('Catalog-proposed-'+version+'.lean.txt')
assert not destination.exists();destination.write_text(proposal)

guard=(p/'guard45.txt').read_text()
roots=['Turing.catalog_ofWords_with_tapes',transfer,copy]
parts=[];guarded=proposal
for i,name in enumerate(roots,1):
 chunk={n:t for n,_,t in chunks(guarded)}[name]
 begin=f'section EndpointPackage{i}\n'+guard+'\n'
 end=f'\n#print axioms {name}\nattribute [simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\nend EndpointPackage{i}\n'
 assert guarded.count(chunk)==1
 guarded=guarded.replace(chunk,begin+chunk+end,1)
 parts.extend([begin,end])
restored=guarded
for piece in parts:
 assert restored.count(piece)==1
 restored=restored.replace(piece,'',1)
assert restored==proposal
(p/('Catalog-sealed-'+version+'.lean.txt')).write_text(guarded)
(p/('seal-'+version+'.json')).write_text(json.dumps({'roots':roots,'definitions':45,'defaults_removed':3,
 'before_each_doc_and_header':True,'inserted_pieces':parts,'exact_source_restoration':True,
 'proposal_sha256':hashlib.sha256(proposal.encode()).hexdigest()},indent=2)+'\n')

A={n:(private,text) for n,private,text in chunks(before)}
B={n:(private,text) for n,private,text in chunks(proposal)}
assert set(B)-set(A)=={'Turing.catalog_ofWords_with_tapes'} and not(set(A)-set(B))
assert B['Turing.catalog_ofWords_with_tapes'][0]
assert [n for n,_,_ in chunks(before)]==[n for n,_,_ in chunks(proposal) if n in A]
changed=[]
for name in A:
 assert A[name][0]==B[name][0]
 if A[name][1]==B[name][1]:continue
 old,new=A[name][1],B[name][1]
 ia,ib=assignment(old),assignment(new)
 assert ia is not None and ib is not None and old[:ia]==new[:ib],name
 assert name in [transfer,copy]
 changed.append(name)
assert set(changed)==({transfer} if version=='v1' else {transfer,copy})
assert re.findall(r'^import .*',before,re.M)==re.findall(r'^import .*',proposal,re.M)
freeze={'existing_declarations':len(A),'proposed_declarations':len(B),'public_before':sum(not v[0] for v in A.values()),
 'public_after':sum(not v[0] for v in B.values()),'new_private_theorem':'Turing.catalog_ofWords_with_tapes',
 'changed_existing_proof_bodies':changed,'all_existing_headers_docstrings_visibility_literal_equal':True,
 'all_other_existing_declaration_chunks_literal_equal':True,'all_existing_order_imports_unchanged':True,
 'actual_source_edited':False,'delimiter':'Balanced depth-zero assignment; handles nested input := x and record fields in target headers.'}
(p/('freeze-'+version+'.json')).write_text(json.dumps(freeze,indent=2)+'\n')
filename='TCSlib/Complexity/TuringMachine/Build/Catalog.lean'
(p/('proposal-'+version+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),proposal.splitlines(True),fromfile='a/'+filename,tofile='b/'+filename)))
print(json.dumps(freeze,indent=2));print((p/('proposal-'+version+'.diff')).read_text())
