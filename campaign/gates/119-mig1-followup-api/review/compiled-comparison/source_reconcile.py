"""Source scope adjunct; compiled environment census remains authoritative for compiler additions."""
from pathlib import Path
import ast,hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4]
spec=importlib.util.spec_from_file_location('P',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
tree=ast.parse((root/'campaign/fills/mig1/landing/review-final-source/source_review.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='split_header');ns={'P':P,'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'trusted-balanced-header','exec'),ns);split=ns['split_header']
ctx=json.loads((out/'context.json').read_text());deltas=[];allold={};allnew={};allattrs=[]
for r in ctx['source_and_olean_pins']:
 stem=Path(r['file']).stem;pair=[]
 for mode in ['base','head']:
  src=(out/(stem+'-'+mode+'.lean.txt')).read_text();rows=[]
  for d in P.decls(src):
   raw=d['raw'];m=re.search(r'(?m)^/(?:--|-!)',raw)
   if m:raw=raw[:m.start()]
   h,delimiter,body=split(raw.rstrip()+'\n');rows.append(dict(d,header_raw=h,body_raw=body,clean_raw=raw.rstrip()+'\n'))
  pair.append({d['name']:d for d in rows})
  # Source attribute commands/annotations are compared separately from changed proof bodies.
  attrs=re.findall(r'(?ms)^\s*(?:@\[[^]]*\]|attribute\s+\[[^]]*\][^\n]*(?:\n\s+[A-Za-z][^\n]*)?)',src)
  allattrs.append({'file':r['file'],'mode':mode,'attribute_texts':attrs})
 a,b=pair;allold.update({n:dict(d,owner_file=r['file']) for n,d in a.items() if not d['private']});allnew.update({n:dict(d,owner_file=r['file']) for n,d in b.items() if not d['private']})
 deltas.append({'file':r['file'],'base_declarations':len(a),'head_declarations':len(b),'added':[n for n in b if n not in a],'removed':[n for n in a if n not in b],'shared_changed_full_header':[n for n in a.keys()&b.keys() if a[n]['header_raw']!=b[n]['header_raw']],'shared_changed_kind_privacy':[n for n in a.keys()&b.keys() if (a[n]['kind'],a[n]['private'])!=(b[n]['kind'],b[n]['private'])],'shared_changed_complete_declaration':[n for n in a.keys()&b.keys() if a[n]['clean_raw']!=b[n]['clean_raw']]})
added=sorted(allnew.keys()-allold.keys());removed=sorted(allold.keys()-allnew.keys());moved=sorted(n for n in allold.keys()&allnew.keys() if allold[n]['owner_file']!=allnew[n]['owner_file'])
assert added==sorted(['Turing.MultiTapeTM.exists_first_entry_of_fixed','Turing.pairDiagTM_spaceUsed','Turing.FinTM.incFixedTM_spaceUsed']) and not removed
assert moved==['Turing.FinTM.redirectTM_spaceUsedByTape']
assert all(not d['shared_changed_full_header'] and not d['shared_changed_kind_privacy'] and not d['shared_changed_complete_declaration'] for d in deltas)
assert allold[moved[0]]['header_raw']==allnew[moved[0]]['header_raw']
assert allold[moved[0]]['clean_raw']!=allnew[moved[0]]['clean_raw']
assert all(a['attribute_texts']==b['attribute_texts'] for a,b in zip(allattrs[::2],allattrs[1::2]))
result={'source_declarations_by_file':deltas,'base_source_public_total':len(allold),'head_source_public_total':len(allnew),'authored_public_additions':added,'authored_public_removals':removed,'same_name_public_home_moves':[{'name':n,'before':allold[n]['owner_file'],'after':allnew[n]['owner_file'],'full_header_identical':True,'proof_body_differs_from_API_baseline':True,'approved_body_adoption_receipt':'campaign/gates/119-mig1-followup-api/source/redirect-home-adoption.json'} for n in moved],'same_owner_old_complete_declarations_and_full_headers_unchanged':True,'source_attribute_annotations_and_commands_unchanged':True,'attribute_snapshots':allattrs,'note':'No source/compiled API exceptions inferred: three additions plus one approved existing-name home move. Source parser is supplemental; compiled census includes every private/internal/generated constant.'}
(out/'source-reconciliation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['attribute_snapshots','source_declarations_by_file']},indent=2))
