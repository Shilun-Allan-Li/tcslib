#!/usr/bin/env python3
"""Static publication review. Reads root sources; runs no Lean and changes no proof file."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import runpy
import subprocess

ROOT=Path('/Users/seyoonr/.codex/worktrees/sc-yao/tcslib-exchange')
OUT=Path(__file__).resolve().parent
lex=runpy.run_path(str(ROOT/'evidence/tools/header_lexer.py'))
inputs={}
def read(path):
    data=path.read_bytes();inputs[str(path.relative_to(ROOT))]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest());return data.decode()
def sha(data):return hashlib.sha256(data).hexdigest()
def line(text,position):return text[:position].count('\n')+1

old_path=ROOT/'evidence/history/pre-final-publication/Garbling.lean'
new_path=ROOT/'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean'
old,new=read(old_path),read(new_path)
a,b=lex['declarations'](old),lex['declarations'](new)
assert len(a)==len(b)==14
assert [d['name'] for d in a]==[d['name'] for d in b]
assert all(x['header']==y['header'] and x['full']==y['full'] for x,y in zip(a,b))
x=next(d for d in a if d['name']=='gateOut_small');y=next(d for d in b if d['name']=='gateOut_small')
ox,oy=x['doc_range'];nx,ny=y['doc_range']
assert old[:ox]==new[:nx] and old[oy:]==new[ny:]
assert new[y['doc_range'][0]:y['doc_range'][1]].count('**Proof sketch.**')==1
old_code=lex['lex'](old)[0];new_code=lex['lex'](new)[0]
assert old_code.split()==new_code.split()
normalized=' '.join(new_code.split()).encode()
actual_marker=list(re.finditer(r':=\s+by\b',y['full']))
assert len(actual_marker)==1
actual_cut=y['start']+actual_marker[0].start()
actual_body=new[actual_cut:y['end']]
assert actual_body.startswith(':= by\n')
assert len(actual_body.splitlines())==15
assert len(actual_body.split(':= by\n',1)[1].splitlines())==14
assert new[y['cut']:].startswith('||')
changes=list(difflib.unified_diff(old.splitlines(),new.splitlines(),fromfile=str(old_path.relative_to(ROOT)),tofile=str(new_path.relative_to(ROOT)),lineterm=''))
insertions=sum(s.startswith('+') and not s.startswith('+++') for s in changes)
deletions=sum(s.startswith('-') and not s.startswith('---') for s in changes)
assert (insertions,deletions)==(5,1)

abbrevs=[];simps=[];explicit_simp=[]
helper_root=ROOT/'TCSlib/Cryptography/SecureComputation/Yao/HybridProof'
for path in sorted(helper_root.rglob('*.lean')):
    source=read(path);code=lex['lex'](source)[0];ds=lex['declarations'](source)
    for d in ds:
        if d['kind']=='abbrev' and 'private ' not in d['header']:
            candidates=[r for r in ds if r['name'].casefold()==(d['name']+'_eq').casefold()]
            assert len(candidates)==1,(path,d['name'])
            reader=candidates[0]
            assert reader['kind'] in ['theorem','lemma'] and 'private ' not in reader['header']
            assert re.search(r':=\s*rfl\s*$',reader['full']),reader['name']
            assert re.search(r'\b'+re.escape(d['name'])+r'\b',reader['header'])
            assert reader['doc_range'] is not None
            abbrevs.append(dict(path=str(path.relative_to(ROOT)),name=d['name'],line=line(source,d['start']),
                definition=d['full'],reader=reader['name'],reader_line=line(source,reader['start']),
                equation=reader['full'],reader_docstring=reader['doc'],same_case=(reader['name']==d['name']+'_eq')))
        attrs=re.findall(r'@\[simps!?\b[^\]]*\]',d['header'],flags=re.S)
        for attr in attrs:
            assert re.search(r'config\s*:=\s*\{\s*isSimp\s*:=\s*false\s*\}',attr),attr
            simps.append(dict(path=str(path.relative_to(ROOT)),declaration=d['name'],line=line(source,d['start']),attribute=attr,isSimp=False))
    explicit_simp.extend(dict(path=str(path.relative_to(ROOT)),line=line(source,m.start()),attribute=m.group(0)) for m in re.finditer(r'@\[\s*simp(?=[\s\]])[^\]]*\]',code))
assert len(abbrevs)==11
assert len(simps)==3
assert not explicit_simp
phase=next(x for x in abbrevs if x['name']=='Phase')
assert phase['reader']=='phase_eq' and phase['reader_line']==144

dec_path=helper_root/'Decryption.lean';dec=read(dec_path)
d=next(d for d in lex['declarations'](dec) if d['name']=='nestedDecTagged_eq')
terminal=re.search(r':=\s*rfl\s*$',d['full']);assert terminal
correct_cut=d['start']+terminal.start()
assert dec[d['cut']:].startswith(':= pairFstD z')
assert d['full'][:terminal.start()].count('let ')==4

summary=dict(scope='Read-only static review; no Lean execution or proof edit',
    root_head=subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip(),
    garbling=dict(before_path=str(old_path.relative_to(ROOT)),current_path=str(new_path.relative_to(ROOT)),
      before_sha256=sha(old.encode()),current_sha256=sha(new.encode()),before_lines=len(old.splitlines()),current_lines=len(new.splitlines()),
      declarations=14,public=13,private=1,order_unchanged=True,all_full_declarations_byte_identical=True,
      lexer_headers_unchanged=True,all_non_doc_source_bytes_identical=True,
      normalized_noncomment_code_sha256=sha(normalized),normalized_noncomment_code_identical=True,
      changed_docstring='gateOut_small',insertions=insertions,deletions=deletions,
      sketch_accurate=True,sketch_mapping=[
        dict(case='zero arguments',proof='cases args; nil; cases k; simp [gateOut_eq_eval, DAGGate.eval_eq]'),
        dict(case='one argument',proof='cons u then nil; cases k; public evaluation readers and List.range_succ'),
        dict(case='two arguments',proof='cons u then cons v then nil; cases k; same public equations'),
        dict(case='three or more arguments',proof='third cons makes length>=3; simp List.length_cons at hfan; omega')],
      proof_line_count_including_marker=15,tactic_lines_after_marker=14,
      lexer_cut_line=line(new,y['cut']),actual_proof_marker_line=line(new,actual_cut),
      parser_qualification='The existing header lexer treats the || Boolean operator inside the theorem type as a match-arm delimiter. Therefore its 17-line proof-sketch candidate count includes type-continuation lines. Full-declaration byte equality and exact one-docstring replacement independently prove no header/body change.'),
    nestedDecTagged_eq=dict(path=str(dec_path.relative_to(ROOT)),line=line(dec,d['start']),
      actual_proof='rfl',type_level_lets=4,proof_term_lines=1,
      lexer_cut_line=line(dec,d['cut']),actual_proof_marker_line=line(dec,correct_cut),
      full_corrected_header=d['full'][:terminal.start()].rstrip(),
      classification='False positive: multiline let expressions belong to the statement; the sole proof term is rfl.'),
    public_abbreviations=abbrevs,public_abbreviation_count=11,all_abbreviations_have_public_rfl_equation_readers=True,
    simps_attributes=simps,simps_attribute_count=3,all_simps_isSimp_false=True,explicit_simp_attributes=explicit_simp,
    input_hashes=inputs,
    qualification='Prepared pre-documentation seals are not claimed to be current-source seal runs by this review. The lead plans four current Garbling seals, a current 261-module sweep and final stored-constant trace.')
(OUT/'REVIEW.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
(OUT/'INPUT-HASHES.json').write_text(json.dumps(inputs,indent=2,ensure_ascii=False)+'\n')
(OUT/'Garbling.diff').write_text('\n'.join(changes)+'\n')
text=['# Final publication review','',
'PASS: the Garbling change is exactly one documentation paragraph. All14 full declarations (13public,1private), their order, headers and bodies are byte-identical; every source byte outside gateOut_small\'s docstring is identical. The diff is5insertions/1deletion,398→402lines. The normalized noncomment code is identical.','',
'The sketch accurately describes the proof: split the gate argument list into zero, one, two, or at least three entries; compute each gate kind via gateOut_eq_eval/DAGGate.eval_eq (plus List.range_succ); exclude the last case using hfan and omega.','',
'Counting qualification: gateOut_small has15 proof-body lines including the :=by marker and14 tactic lines after it. The existing lexer cuts at Boolean || in the TYPE, so the publication audit\'s17candidate lines include type continuation. The added sketch remains appropriate and accurate. Decryption.nestedDecTagged_eq is a separate false positive: four statement-level lets span the type, while its only proof term is rfl. No change to that declaration is needed.','',
'## Public abbreviation readers','',
'All11 public abbreviations have a public same-file equation theorem with body rfl and a docstring. ChunkScanner.Phase intentionally uses lowercase phase_eq (line144), whose equation is Phase=(Bool×Bool×Bool).','',
'| Module | Abbreviation | Reader | Reader line |','|---|---|---|---:|']
for a in abbrevs:text.append(f"| {Path(a['path']).stem} | `{a['name']}` | `{a['reader']}` | {a['reader_line']} |")
text += ['', '## Generated reader attributes','',
'All3 simps attributes explicitly use `(config := { isSimp := false })`. No explicit simp attribute occurs in the helper code.','',
'| Module | Definition | Attribute line |','|---|---|---:|']
for s in simps:text.append(f"| {Path(s['path']).stem} | `{s['declaration']}` | {s['line']} |")
text += ['', 'This report runs no Lean, edits no proof source, and certifies only the static publication repair. The lead\'s current-source4Garbling seals, full current261module sweep and stored-constant trace remain distinct required evidence. Full equations, attributes, source hashes, the exact diff and parser qualifications are in REVIEW.json and companion files.']
(OUT/'REPORT-fragment.md').write_text('\n'.join(text)+'\n')
manifest=[]
for p in sorted(OUT.iterdir()):
    if p.is_file() and p.name!='SHA256SUMS':manifest.append(sha(p.read_bytes())+'  '+p.name)
(OUT/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
for row in manifest:
    h,n=row.split(None,1);assert sha((OUT/n).read_bytes())==h
print(json.dumps(dict(path=str(OUT),files=len(manifest),report_sha256=sha((OUT/'REPORT-fragment.md').read_bytes()),manifest_sha256=sha((OUT/'SHA256SUMS').read_bytes()),doc_only=True,public_abbrevs=11,simps=3)))
