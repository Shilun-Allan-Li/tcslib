"""Inspect exact top-level rewrite/simplifier rule heads in the 63 sealed source regions."""
from pathlib import Path
import json,re,sys,importlib.util
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];spec=importlib.util.spec_from_file_location('c',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
text=(out/'milestone3-source.lean.txt').read_text();decls={d['name']:d for d in m.decls(text)};man=json.loads((out/'Final-sections-sealed-v2-manifest.json').read_text());names=[r['name'] for r in man['regions']];extra=set(json.loads((out/'milestone3-freeze.json').read_text())['additional_strong_seal_targets'])
forbidden=set(man['definitions'])|{n.removeprefix('Turing.') for n in man['definitions']}|{n.removeprefix('Turing.FinTM.') for n in man['definitions'] if n.startswith('Turing.FinTM.')}|{'SignType.cast','Function.update','Fin.addCases','Fin.cases','Function.comp','Bool.toNat'}
rows=[];bad=[];opaque=[]
for name in names:
 s=decls[name]['code']
 for mt in re.finditer(r'\b(simp|simpa|simp_all|simp_rw|rw|rewrite)(?:\s+only)?\s*\[',s):
  start=mt.end();stack=['['];i=start;last=start;items=[]
  while stack:
   c=s[i]
   if c in '[({⟨':stack.append(c)
   elif c in '])}⟩':
    stack.pop()
    if not stack:items.append(s[last:i].strip());break
   elif c==',' and len(stack)==1:items.append(s[last:i].strip());last=i+1
   i+=1
  for entry in items:
   head=re.match(r'(?:←\s*)?([A-Za-z_][\w.\'?!]*)',entry)
   head=head[1] if head else None
   r={'declaration':name,'new_factoring_region':name in extra,'tactic':mt[1],'entry':entry,'rule_head':head};rows.append(r)
   if head in forbidden:bad.append(r)
   for op in ['pairEncode','pairDecode','dbl']:
    if re.search(r'\b'+op+r'\b',entry) and head!=op:opaque.append(dict(r,opaque_value=op))
 for mt in re.finditer(r'\bunfold\s+([^\n;]+)',s):
  items=mt[1].split(' at ')[0].strip().split()
  for head in items:
   r={'declaration':name,'new_factoring_region':name in extra,'tactic':'unfold','entry':head,'rule_head':head};rows.append(r)
   if head in forbidden:bad.append(r)
assert not bad,bad
result={'source_sha256':man['source_sha256'],'sections':len(names),'argument_entries':len(rows),'forbidden_rule_heads':bad,'checked_foreign_and_core_definition_names':sorted(forbidden),'new_factoring_rule_heads':sorted({r['rule_head'] for r in rows if r['new_factoring_region'] and r['rule_head']}),'opaque_operation_parameters':opaque,'all_argument_entries':rows,'scope':'Rule-head inspection plus actual seals; opaque operation-valued theorem arguments are not unfolding rules. Whole unchanged T1 legacy caller bodies are excluded from this strong-region population.'}
(out/'final37-argument-scan.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['sections','argument_entries','forbidden_rule_heads','new_factoring_rule_heads','opaque_operation_parameters']},indent=2))
