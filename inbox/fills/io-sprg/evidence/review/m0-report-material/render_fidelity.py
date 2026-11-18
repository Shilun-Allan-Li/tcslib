from pathlib import Path
import csv,json,re
out=Path('/private/tmp/io-sprg-report');meta=json.loads((out/'source-snapshot.json').read_text())
rows=list(csv.DictReader((out/'fidelity-declarations.tsv').open(),delimiter='\t'))
def ref(m):
 key=m[1];matches=[r for r in rows if r['Lean_name'].endswith('.'+key) or r['Lean_name']==key]
 if len(matches)!=1:raise ValueError((key,[(r['Lean_name'],r['file_line']) for r in matches]))
 row=matches[0];loc=row['file_line'].split('StructuredSeed/',1)[-1]
 return f"`{key}` (`{loc}`)"
s=(out/'fidelity-template.md').read_text().replace('CANDIDATE',meta['candidate'])
s=re.sub(r'@([^@\n]+)@',ref,s)
(out/'fidelity.md').write_text(s)
print('Wrote fidelity.md:',len(s.splitlines()),'lines')
