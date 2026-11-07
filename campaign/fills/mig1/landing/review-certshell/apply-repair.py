"""Compare-and-swap the one owned proof after strict success and a full source freeze."""
from pathlib import Path
import datetime
import difflib
import hashlib
import importlib.util
import json
import re
import sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
context=json.loads((OUT/'setup.json').read_text())
source=Path(context['owned_source'])
old=(OUT/'CertShell-start.lean.txt').read_text()
new=(OUT/'CertShell-proposed-v2.lean.txt').read_text()
assert hashlib.sha256(source.read_bytes()).hexdigest()==context['source_sha256']
for name in ['CertShell-strict-v3','CertShell-initializer-diagnostic-v1','Controls-unsealed-v2']:
    r=json.loads((OUT/(name+'-run.json')).read_text());assert r['exit']==r['errors']==0,name
assert json.loads((OUT/'Controls-sealed-v2-run.json').read_text())['errors']==82
spec=importlib.util.spec_from_file_location('s',ROOT/'campaign/gates/106-sg1-dedup/review/round2-current/source_tools.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
r=s.compare(old,new)
assert not any(r[k] for k in ['public_added','public_removed','visibility_changes','public_header_changes','public_definition_changes','public_proof_changes','private_added','private_removed'])
assert r['public_order_unchanged'] and r['imports_before']==r['imports_after']
assert [d['name'] for d in r['private_changed']]==['Turing.cert_prepare_exists']
before,after=[{d['name']:d for d in s.decls(t)} for t in [old,new]]
assert list(before)==list(after)
assert all(before[n]['header']==after[n]['header'] for n in before)
assert all(before[n]['raw']==after[n]['raw'] for n in before if n!='Turing.cert_prepare_exists')
assert not re.search(r'\b(?:sorry|admit)\b',s.clean(new))
start=old.index('private theorem cert_prepare_exists');suffix='\n\n/-- **The certificate shell**'
assert old[:start]==new[:start] and old[old.index(suffix,start):]==new[new.index(suffix,start):]
target=after['Turing.cert_prepare_exists']
foreign=set(json.loads((OUT/'seal-inventory.json').read_text())['definitions'])
short={n.split('.')[-1]:n for n in foreign}
argscan=[];bad=[]
for m in re.finditer(r'\b(simp(?:_all)?|simpa|rw|unfold|dsimp)\b[^\n]*',target['code']):
    # Retain full physical tactic lines; following indented list lines are retained below too.
    line=target['start']+target['code'][:m.start()].count('\n')
    argscan.append(dict(line=line,text=m[0]))
for m in re.finditer(r'\[(.*?)\]',target['code'],re.S):
    for name in re.findall(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',m[1]):
        if name in foreign or name in short:
            bad.append(dict(name=name,arguments=m[1]))
assert not bad,bad
(OUT/'argument-inspection.json').write_text(json.dumps(dict(tactic_lines=argscan,explicit_foreign_definition_arguments=bad,method='Balanced-header target extraction; every bracket argument scanned for the sealed ordinary definition names, plus manual rw/simp/unfold/show/change inspection.'),indent=2)+'\n')
(OUT/'certshell-repair.diff').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='received/CertShell.lean',tofile='repaired/CertShell.lean')))
source.write_text(new)
(OUT/'CertShell-final.lean.txt').write_bytes(source.read_bytes())
record=dict(at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=context['owned_source'],old_sha256=context['source_sha256'],new_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_freeze=r,
    all_surviving_public_and_private_headers_unchanged=True,all_other_declaration_bytes_unchanged=True,imports_order_definitions_tables_unchanged=True,
    old_local_witness='let D : FinTM Bool := ⟨K, _, M₅⟩',
    new_local_witness='let D : FinTM Bool := ⟨K, _, {M₅ with q₀ := .inl (.inl (.inl (.inl (.inl SweepPhase.sweep))))}⟩',
    initializer_diagnostic='Unsealed diagnostic actually proves M₅.q₀ equals explicit label, D.tm=M₅, and D.tm.tr=M₅.tr by rfl. No such foreign reduction is in production.',
    production_transport='MultiTapeTM.runFrom_with_q₀; explicit local q₀ avoids a foreign machine-shape read.',
    actual_source_applied=True,committed=False,pushed=False,other_files_edited=False)
(OUT/'application.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(applied=True,sha256=record['new_sha256'],changed_private='Turing.cert_prepare_exists',other_declaration_bytes_unchanged=True),indent=2))
