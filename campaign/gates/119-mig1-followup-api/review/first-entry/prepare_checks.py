from pathlib import Path
import hashlib,json,sys,re,ast,importlib.util
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];actual=(out/'actual-Finite.lean.txt').read_text();insert=(out/'inserted-approved-theorem.lean.txt').read_text();guard='section\nattribute [local irreducible] Turing.MultiTapeTM.step Turing.MultiTapeTM.runFrom\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n';assert actual.count(insert)==1
sealed=actual.replace(insert,guard+insert+'end\n\n',1);assert sealed.replace(guard+insert+'end\n\n',insert,1)==actual
sealed+='\n#print axioms Turing.MultiTapeTM.exists_first_entry_of_fixed\n';(out/'Finite-newsection-sealed.lean.txt').write_text(sealed);(out/'guard.txt').write_text(guard)
control=(root/'campaign/fills/mig1/review/first-entry-proposal/Controls-unsealed-v2.lean.txt').read_text();control=control.replace('open Turing\n','open Turing\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n',1);(out/'Controls-unsealed.lean.txt').write_text(control);sc=control.replace('open Turing\n','open Turing\nattribute [local irreducible] Turing.MultiTapeTM.step Turing.MultiTapeTM.runFrom\n',1);(out/'Controls-sealed.lean.txt').write_text(sc)
# Trusted balanced header reader, copied as a pure function; no previous review module executed.
spec=importlib.util.spec_from_file_location('P',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P);tree=ast.parse((root/'campaign/fills/mig1/landing/review-final-source/source_review.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='split_header');ns={'P':P,'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'trusted-balanced-header','exec'),ns);split=ns['split_header']
def decls(s):
 rows=[]
 for d in P.decls(s):
  raw=d['raw'];m=re.search(r'(?m)^/(?:--|-!)',raw)
  if m:raw=raw[:m.start()]
  h,delimiter,b=split(raw.rstrip()+'\n');rows.append(dict(d,raw=raw.rstrip()+'\n',header_raw=h,body=b))
 return rows
old=decls((out/'before-Finite.lean.txt').read_text());new=decls(actual);a={d['name']:d for d in old};b={d['name']:d for d in new};n='Turing.MultiTapeTM.exists_first_entry_of_fixed';assert set(b)-set(a)=={n} and not set(a)-set(b);assert not b[n]['private'] and b[n]['kind']=='theorem';assert [d['name'] for d in old]==[d['name'] for d in new if d['name']!=n];assert all(a[k]['raw']==b[k]['raw'] and a[k]['header_raw']==b[k]['header_raw'] and a[k]['private']==b[k]['private'] and a[k]['kind']==b[k]['kind'] for k in a)
assert b[n]['raw'].strip()==(out/'approved-contract.lean.txt').read_text().strip();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',P.clean(b[n]['raw']))
freeze={'old_source_declarations':len(old),'new_source_declarations':len(new),'old_public_declarations':sum(not d['private'] for d in old),'new_public_declarations':sum(not d['private'] for d in new),'old_full_headers_and_complete_declaration_bytes_equal':True,'all_old_visibility_kind_order_equal':True,'only_added':n,'new_header_and_proof_exact_approved_source':True,'imports_attrs_runtime_defs_old_comments_all_old_bytes_frozen':True,'seal_guard_before_doc_and_complete_header':True,'seal_exact_removal_restores_actual_bytes':True,'source_sha256':hashlib.sha256(actual.encode()).hexdigest(),'source_line':b[n]['start'],'source_body_end_line':b[n]['start']+len(b[n]['raw'].splitlines())-1};(out/'source-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n');print(json.dumps(freeze,indent=2))
