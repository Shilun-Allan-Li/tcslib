#!/usr/bin/env python3
"""Map every raw seal diagnostic to a declaration, preserving both Lean error forms."""
import importlib.util
import json
from pathlib import Path
import re
spec=importlib.util.spec_from_file_location('headers','evidence/tools/check_headers.py')
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
root=Path('evidence/seals')
all_rows=[]
for phase in ['base','final']:
 manifest=json.loads((root/phase/'manifest.json').read_text())
 result_paths=sorted(Path('evidence/logs').glob('seals-'+phase+'*/results.jsonl'))
 if not result_paths:continue
 lookup={}
 for results in result_paths:
  lookup.update({r['module']:r for r in map(json.loads,results.read_text().splitlines())})
 for row in manifest:
  if 'probe'not in row:continue
  module=row['probe'][:-5]
  if module not in lookup:continue
  result=lookup[module];raw=Path(result['log']).read_text()
  lines=Path(result['log']).with_suffix('.source.lean').read_text().splitlines(True)
  i=row['original_insert_line'];k=row['inserted_lines']
  original=''.join(lines[:i]+lines[i+k:])
  decls=h.declarations(original)
  errors=[]
  pattern=r'^(\S+\.lean):(\d+):(\d+): error[:(]'
  for m in re.finditer(pattern,raw,re.M):
   probe_line=int(m[2]);line=probe_line-k if probe_line>i+k else probe_line
   offset=sum(len(l)for l in original.splitlines(True)[:line-1])
   preceding=[d for d in decls if d['start']<=offset]
   decl=preceding[-1]['name']if preceding else '<preamble>'
   rest=raw[m.start():]
   boundary=re.search(r'\n(?:\S+\.lean:\d+:\d+: (?:error|warning|info)|FAIL\(|END )',rest[1:])
   detail=rest[:boundary.start()+1]if boundary else rest.split('\n        ')[0]
   errors.append(dict(declaration=decl,source_line=line,probe_line=probe_line,
                      diagnostic=detail.rstrip()))
  assert len(errors)==result['errors'],(module,len(errors),result['errors'])
  count=re.search(r'SEAL_COUNTS requested=(\d+) excluded=(\d+)',raw)
  assert count,(module,'missing seal counts')
  all_rows.append(dict(phase=phase,file=row['file'],variant=row['variant'],
      coercions=row['coercions'],exit=result['exit'],errors=errors,
      sealed=int(count[1]),excluded=int(count[2]),log=result['log']))
(root/'analysis.json').write_text(json.dumps(all_rows,indent=2)+'\n')
report=['# Whole-file seal diagnostic inventory','',
 '| Phase | File | Variant | Coercions | Errors | Declarations |',
 '|---|---|---|---|---:|---|']
for row in all_rows:
 names=', '.join(dict.fromkeys(e['declaration']for e in row['errors']))or '—'
 report.append('| '+ ' | '.join([row['phase'],row['file'].split('/')[-1],row['variant'],
   row['coercions'],str(len(row['errors'])),names])+' |')
(root/'inventory.md').write_text('\n'.join(report)+'\n')
print('ANALYZED',len(all_rows),'completed seals; diagnostic count',sum(len(r['errors'])for r in all_rows))
for row in all_rows:
 if row['errors']:print(row['phase'],row['file'],row['variant'],row['coercions'],
   [(e['declaration'],e['source_line'])for e in row['errors']])
