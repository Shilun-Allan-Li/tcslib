# io-sprg source inventory, Mac host 2026-11-18. No Lean; lexical, not typed evidence.
import csv,hashlib,json,re,runpy,subprocess
from pathlib import Path
root=Path.cwd();parse=runpy.run_path(str(root/'evidence/tools/clash/clash_scan.py'))['parse_decls'];files=(root/'evidence/tools/io-sprg-rule10/files.txt').read_text().split();head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();out=root/'evidence/statements';out.mkdir(exist_ok=True)
old={r['Lean_name']:r for r in csv.DictReader((root/'evidence/review/m0-report-sp-w2/proof-obligations.tsv').open(),delimiter='\t')}
rows=[];holes=[];anonymous=[]
for f in files:
 text=(root/f).read_text();lines=text.splitlines();decls=parse(text)
 for ix,d in enumerate(decls):
  j=d['line']-2
  while j>=0 and(not lines[j].strip() or lines[j].startswith('omit ')):j-=1
  doc=''
  if j>=0 and lines[j].rstrip().endswith('-/'):
   k=j
   while k>=0 and '/--' not in lines[k]:k-=1
   if k>=0:doc='\n'.join(lines[k:j+1]).strip()[3:-2].strip()
  prose=' '.join(doc.split('**Proof sketch.**',1)[0].split());tag=re.search(r'\[JLS26,\s*([^]]+)\]',prose)
  rows.append(dict(Lean_name=d['full'],file_line=f+':'+str(d['line']),kind=d['kind'],paper_item_page_tag=tag[1] if tag else 'No declaration-level JLS tag; inspect owning section/module or glue prose',deviations=','.join(sorted(set(re.findall(r'Dv\d+|SP-W\d+',doc)))),statement_prose=prose))
  end=decls[ix+1]['line']-1 if ix+1<len(decls) else len(lines);chunk='\n'.join(lines[d['line']-1:end]);has=re.search(r':=\s*(?:by\s+)?sorry\b',chunk)
  if has:
   assert d['kind'] in ['theorem','lemma'],d
   assert '**Proof sketch.**' in doc,d
   assert d['full'] in old,d
   holes.append(dict(Lean_name=d['full'],file_line=f+':'+str(d['line']),milestone=old[d['full']]['milestone'],owner_proof_sketch=' '.join(doc.split('**Proof sketch.**',1)[1].split())))
assert len(rows)==670 and len(holes)==146,(len(rows),len(holes));assert {r['Lean_name'] for r in holes}==set(old)
for name,data in [('fidelity-current.tsv',rows),('proof-obligations-current.tsv',holes)]:
 with(out/name).open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(data[0]),delimiter='\t');w.writeheader();w.writerows(data)
(out/'source-inventory-binding.json').write_text(json.dumps(dict(head=head,named_headers=len(rows),named_sorry_bodies=len(holes),qualification='Lexical source headers/docstrings; full generated public constants and kernel types are in StmtDump.',source_sha256={f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files}),indent=1)+'\n');print('SOURCE_INVENTORY',len(rows),'named headers;',len(holes),'named sorry bodies; all sketches present')
