from pathlib import Path
import json,re,collections,difflib
O=Path(__file__).parent;summary={}
def key(row,kind):
 path=row['path'];msg=row['message']
 if kind=='style':m=re.match(re.escape(path)+r'(?::\d+)?: (.*)',msg);assert m;msg=m.group(1)
 else:msg=re.sub(r'^line \d+: ','',msg)
 msg=re.sub(r'^\d+ lines(?=;| \(>| >)','<N> lines',msg);msg=re.sub(r'proof is \d+ lines','proof is <N> lines',msg);return(path,row.get('level','FINDING'),msg)
for kind in ['style','campaign']:
 side={};groups={}
 for name in ['BASE','HEAD']:
  side[name]=json.loads((O/(name+'-'+kind+'-findings.json')).read_text());groups[name]=collections.defaultdict(list)
  for r in side[name]['findings']:groups[name][key(r,kind)].append(r)
 rows=[]
 for identity in sorted(set(groups['BASE'])|set(groups['HEAD'])):
  a=groups['BASE'].get(identity,[]);b=groups['HEAD'].get(identity,[]);new=max(0,len(b)-len(a));removed=max(0,len(a)-len(b));disposition='inherited; retain actual raw findings and source-size/position differences'
  if new and kind=='style' and identity[0]=='TCSlib/Complexity/Diagonalization.lean' and ('public `theorem and`' in identity[2] or '`and` proof' in identity[2]):disposition='NEW linter parser false positive: line28 is inside module doc comment, no theorem and or proof in actual Lean code. Root doc-only wording repair proposed; not inherited and not called clean.'
  elif new and kind=='campaign' and identity[1]=='INFO':disposition='NEW source-context INFO for the authorized new Ladner file; no FAIL/WARN severity'
  rows.append({'identity':identity,'BASE':a,'HEAD':b,'new_occurrences':new,'removed_occurrences':removed,'inherited_occurrences':min(len(a),len(b)),'disposition':disposition})
 (O/(kind+'-dispositions.json')).write_text(json.dumps(rows,indent=2)+'\n');levels=lambda s:dict(collections.Counter(r.get('level','FINDING') for r in side[s]['findings']));summary[kind]={'BASE_exit':side['BASE']['exit'],'HEAD_exit':side['HEAD']['exit'],'BASE_count':len(side['BASE']['findings']),'HEAD_count':len(side['HEAD']['findings']),'BASE_levels':levels('BASE'),'HEAD_levels':levels('HEAD'),'new_occurrences':sum(r['new_occurrences'] for r in rows),'removed_occurrences':sum(r['removed_occurrences'] for r in rows),'inherited_occurrences':sum(r['inherited_occurrences'] for r in rows),'normalization':'Only source line locations and dynamic source/proof line counts; raw messages retained.'};a=(O/('BASE-'+kind+'.txt')).read_text();b=(O/('HEAD-'+kind+'.txt')).read_text();(O/(kind+'.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile='BASE-'+kind,tofile='HEAD-'+kind)))
A={r['path']:r for r in json.loads((O/'BASE-size.txt').read_text())};B={r['path']:r for r in json.loads((O/'HEAD-size.txt').read_text())};sizes=[]
for path in sorted(set(A)|set(B)):
 a=A.get(path);b=B.get(path);sizes.append({'path':path,'BASE':a,'HEAD':b,'BASE_absent':a is None,'delta_bytes':b['bytes']-a['bytes'] if a and b else None,'delta_lines':b['lines_splitlines']-a['lines_splitlines'] if a and b else None,'new_file_not_fake_zero_length_baseline':a is None})
(O/'size-dispositions.json').write_text(json.dumps(sizes,indent=2)+'\n');summary['sizes']=sizes;(O/'comparison.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
