"""Map each raw diagnostic to its original declaration; retain complete raw blocks."""
from pathlib import Path
import json,re
root=Path('evidence/subagents/a2')
rows=[]
for p in (root/'probe-runs').glob('*/results.jsonl'):
 rows += [json.loads(x) for x in p.read_text().splitlines() if x.strip()]
failures=[]
for row in rows:
 if not row.get('errors') or 'file' not in row:continue
 raw=Path(row['log']).read_text()
 source=Path(row['probe']).read_text().splitlines()
 starts=list(re.finditer(r'^(\S+\.lean):(\d+):(\d+): error[:(].*$',raw,re.M))
 for j,m in enumerate(starts):
  line=int(m[2]);decl='seal preamble'
  for s in reversed(source[:line]):
   d=re.match(r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:(]+)',s)
   if d:decl=d[1];break
  end=starts[j+1].start() if j+1<len(starts) else len(raw)
  failures.append({'file':row['file'],'variant':row['variant'],'coercions':row['coercions'],
   'log':row['log'],'probe_line':line,'original_line':line-row['inserted_lines'],
   'declaration':decl,'diagnostic':raw[m.start():end].strip()})
(root/'failure-attribution.json').write_text(json.dumps(failures,indent=2)+'\n')
counts={}
for f in failures:
 key=f['file']+':'+f['declaration']
 counts[key]=counts.get(key,0)+1
print(json.dumps({'completed_runs':len(rows),'failing_diagnostics':len(failures),'declarations':counts},indent=2))
