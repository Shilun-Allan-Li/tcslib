"""Verify the bounded hypothetical adapter, controls, source pins and import delta."""
from pathlib import Path
import collections
import hashlib
import json
import re

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
context=json.loads((OUT/'context.json').read_text())
guards=(OUT/'guard-definitions.txt').read_text().splitlines()
guard='attribute [local irreducible] '+' '.join(guards)+'\n'
native=(OUT/'Candidate-native-v1.lean.txt').read_text()
sealed=(OUT/'Candidate-sealed-v1.lean.txt').read_text()
assert sealed.replace(guard+'\n','',1)==native
assert sealed.index(guard)<sealed.index('namespace Complexity')<sealed.index((OUT/'exact-production-header.txt').read_text())
positive=(OUT/'Controls-unsealed-v1.lean.txt').read_text()
negative=(OUT/'Controls-sealed-v1.lean.txt').read_text()
assert negative.replace(guard+'\n','',1)==positive
imports=(OUT/'hypothetical-imports.txt').read_text()
assert native.startswith(imports) and positive.startswith(imports)
pins=json.loads((OUT/'input-pins.json').read_text())
for name,row in pins.items():
    p=Path(name);assert p.stat().st_size==row['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
for stem in ['Inventory-v1','Candidate-native-v1','Candidate-sealed-v1','Controls-unsealed-v1']:
    run=json.loads((OUT/(stem+'-run.json')).read_text());assert run['exit']==run['errors']==0
    assert hashlib.sha256((OUT/(stem+'.lean.txt')).read_bytes()).hexdigest()==run['input_sha256']
    assert hashlib.sha256((OUT/(stem+'.out')).read_bytes()).hexdigest()==run['output_sha256']
control=json.loads((OUT/'control-check.json').read_text())
assert control['all_exact_multiplicities_match'] and control['pointwise_and_abstracted_pairs']==8
a=(OUT/'Candidate-native-v1.out').read_text();b=(OUT/'Candidate-sealed-v1.out').read_text();assert a==b
proofs=[]
for m in re.finditer(r'^PROOFAX\|([^|\n]+)\|kind=([^|\n]+)\|\[([^\]]*)\]',a,re.M):
    proofs.append(dict(name=m[1],kind=m[2],axioms=[x.strip() for x in m[3].split(',') if x.strip()]))
assert len(proofs)==3 and all(set(x['axioms'])<={'propext','Quot.sound'} for x in proofs)
ordinary=set(re.findall(r'^FOREIGNDEF\|[^|\n]+\|([^|\n]+)\|[^|\n]+\|hints=regular$',a,re.M))
assert ordinary==set(guards)
assert not re.search(r'^CITED\|.*\|private=true$',a,re.M)
homes=sorted(set(re.findall(r'^CITED\|[^|\n]+\|[^|\n]+\|([^|\n]+)\|',a,re.M)))
assert 'Complexity.length_pair_components_le' in a
assert '.eq_def' not in native and '.eq_1' not in native
for term in ['[pairDecode','[pairEncode','[pairFstD','[pairSndD','unfold ']:
    assert term not in (OUT/'proposed-body.txt').read_text()
inventory=(OUT/'Inventory-v1.out').read_text()
assert len(re.findall(r'^ORDINARY\|.*\|simp=false\|unfold=false$',inventory,re.M))==4

# Reuse the trusted standing import parser/functions only, never delivery scripts.
script=ROOT/'campaign/gates/106-sg1-dedup/review/round3-prefix-repair/import-closure.py'
prefix=script.read_text().split("before=(OUT/'Hardness-before.lean.txt')",1)[0]
old="TARGET=c['owned_file'].removesuffix('.lean').replace('/','.')"
assert prefix.count(old)==1
prefix=prefix.replace(old,"TARGET='TCSlib.Complexity.CookLevin.Hardness'")
scope={'__file__':str(OUT/'import-functions.py')}
exec(compile(prefix,str(script),'exec'),scope)
source=Path(context['worktree'])/'TCSlib/Complexity/CookLevin/Hardness.lean'
before=source.read_text()
first_import=next(line+'\n' for line in before.splitlines() if line.startswith('import '))
assert before.count(first_import)==1
after=before.replace(first_import,'import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop\n'+first_import,1)
base,be,bm=scope['closure'](before,False);head,he,hm=scope['closure'](after,False)
assert not bm and not hm and not base-head
done=set();active=set()
def check_cycle(module):
    if module in done:return
    assert module not in active,'hypothetical import cycle'
    active.add(module)
    for child in he[module]:
        if child in head:check_cycle(child)
    active.remove(module);done.add(module)
for module in sorted(head):check_cycle(module)
added=sorted(head-base)
newpins={}
for module in added:
    sp=scope['source_path'](module);op=scope['olean_path'](module)
    assert sp is not None and op is not None
    newpins[module]=dict(source=str(sp),source_sha256=hashlib.sha256(sp.read_bytes()).hexdigest(),
                         olean=str(op),olean_sha256=hashlib.sha256(op.read_bytes()).hexdigest())
fb,_,fm=scope['closure'](before,True);fh,_,fhm=scope['closure'](after,True)
assert not fm and not fhm
missing=[m for m in fh if scope['olean_path'](m) is None];assert not missing
graph=dict(status='Hypothetical source-header closure only; production import unchanged',
           TCSlib_before=len(base),TCSlib_after=len(head),TCSlib_added=added,new_module_pins=newpins,
           full_Core_package_before=len(fb),full_Core_package_after=len(fh),full_added=sorted(fh-fb),
           missing_compiled_modules=missing,TCSlib_source_graph_acyclic=True)
(OUT/'hypothetical-import-delta.json').write_text(json.dumps(graph,indent=2)+'\n')
result=dict(status='Passed hypothetical exact-header adapter; new import unapproved, production unchanged',
            guard_definitions=guards,default_simp_definitions_to_disable=[],
            guard_before_header_doc_and_helpers=True,guard_removal_exact_native_identity=True,
            native_sealed_metadata_identical=True,proof_AX=proofs,direct_cited_homes=homes,
            direct_foreign_ordinary_definitions=sorted(ordinary),no_imported_private_reference=True,
            public_named_readers_present_before_use=True,no_generated_equation_query_or_materialization=True,
            paired_controls=8,control_checker_rejection_cases=control['checker_negative_cases'],
            explicit_arguments_review='change unfolds only the two literal same-home clHeader definitions; foreign pairDecode remains symbolic. simp only uses Option/List theorems, the inverse equality, and published projection equations. No foreign ordinary definition is an unfold/rw/simp argument.',
            production_input_hashes_unchanged=True,full_production_module_recompile=False,
            limits='No new import approved/applied, no whole Hardness or merged replay with that import, no seal of upstream legacy theorem proofs, no gate clearance.')
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(standard_AX_roots_descendants=len(proofs),opaque_guard_defs=len(guards),paired_controls=8,TCSlib_imports_before=len(base),TCSlib_imports_after=len(head),TCSlib_added=added),indent=2))
