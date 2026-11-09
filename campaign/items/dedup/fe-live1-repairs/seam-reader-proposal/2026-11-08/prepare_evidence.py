from pathlib import Path
import json,hashlib,re,difflib
out=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
base=(out/'source/Hardness-BASE.lean.txt').read_text();hyp=(out/'source/Hardness-HYP.lean.txt').read_text();reversed_source=hyp;rows=[]
for name in ['clFresh_idle','clPrepared_idle']:
 def split(t):
  start=t.index('private lemma '+name+' ');sep=t.index(':= by\n',start)+len(':= by\n');end=t.index('\n/--',sep);return t[start:sep],t[sep:end]
 bh,bb=split(base);hh,hb=split(hyp);assert bh==hh;assert reversed_source.count(hb)==1;reversed_source=reversed_source.replace(hb,bb)
 rows.append({'name':name,'literal_formal_header_exact':bh==hh,'formal_header_sha256':sha(bh.encode()),'BASE_body_sha256':sha(bb.encode()),'HYP_body_sha256':sha(hb.encode()),'HYP_body_lines':len(hb.strip().splitlines())})
old_doc='''/-- An absorbing return in the prepared machine remains absorbing after
native loading, with the complete retained-input frame fixed. -/'''
new_doc='''/-- An absorbing return in the prepared machine remains absorbing after
native loading, with the complete retained-input frame fixed.

**Proof sketch.** Reconstruct the supplied configuration as the forwarding
embedding of its selected source tapes and unchanged ambient frame. The
source return is fixed by its control-action contract. The embedding's
one-step lockstep and the seam's right transition preserve that fixed point. -/'''
assert reversed_source.count(new_doc)==1;reversed_source=reversed_source.replace(new_doc,old_doc);assert reversed_source==base
api=(out/'source/API-statement.lean.txt').read_text();sb=(out/'source/Seam-BASE.lean.txt').read_text();sh=(out/'source/Seam-HYP.lean.txt').read_text();assert sh.count(api)==1;assert sh.replace(api,'')==sb
for n,t in [('Hardness',hyp),('Seam',sh)]:
 assert (out/'project'/('TCSlib/Complexity/CookLevin/Hardness.lean' if n=='Hardness' else 'TCSlib/Complexity/TuringMachine/Build/Seam.lean')).read_text()==t
record={'source_commit':'9936345ae64a4380bbec3ac6f3dad192f927420a','selected':rows,'all_other_consumer_source_bytes_exact_after_reversing_two_bodies_and_one_sketch':True,'imports_exact':True,'existing_definitions_exact':True,'formal_headers_exact':True,'new_public_declarations':['Turing.seamCompTM_tr_inr'],'new_private_declarations':[],'new_imports':[],'new_definitions':[],'new_attributes':[],'producer_all_other_bytes_exact_after_removing_one_API':True,'Seam_BASE_sha256':sha(sb.encode()),'Seam_HYP_sha256':sha(sh.encode()),'Hardness_BASE_sha256':sha(base.encode()),'Hardness_HYP_sha256':sha(hyp.encode())}
(out/'SOURCE-FREEZE.json').write_text(json.dumps(record,indent=2)+'\n')
closure=json.loads((out/'inputs/import-source-closure.json').read_text());mapping={r['path']:r for r in json.loads((out/'inputs/current-all-Lean-blob-map.json').read_text())}
for row in closure['rows']:
 path=row['path'];data=(out/'source/Hardness-BASE.lean.txt').read_bytes() if path.endswith('/CookLevin/Hardness.lean') else (out/'source/Seam-BASE.lean.txt').read_bytes() if path.endswith('/Build/Seam.lean') else (out/'project'/path).read_bytes();assert sha(data)==mapping[path]['sha256'];f=out/'inputs/source-at-current'/(path+'.txt');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
print(json.dumps(record,indent=2))
