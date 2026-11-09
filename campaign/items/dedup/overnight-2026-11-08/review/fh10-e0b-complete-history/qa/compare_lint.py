from pathlib import Path
import json,re,collections,difflib,hashlib
O=Path(__file__).parent;summary={};allrows=[]
def identify(row,kind):
 path=row['path'];msg=row['message'];line=None
 if kind=='style':
  m=re.match(re.escape(path)+r'(?::(\d+))?: (.*)',msg);assert m,msg;line=int(m.group(1)) if m.group(1) else None;msg=m.group(2)
 else:
  m=re.match(r'line (\d+): (.*)',msg)
  if m:line=int(m.group(1));msg=m.group(2)
 norm=re.sub(r'^\d+ lines (?=>|\(>)','<N> lines ',msg);norm=re.sub(r'proof is \d+ lines','proof is <N> lines',norm);norm=re.sub(r'^\d+ lines;','<N> lines;',norm)
 return (path,row.get('level','FINDING'),norm),line,msg
for kind in ['style','campaign']:
 byside={}
 for side in ['BASE','HEAD']:
  d=json.loads((O/(side+'-'+kind+'-findings.json')).read_text());group=collections.defaultdict(list)
  for row in d['findings']:
   key,line,msg=identify(row,kind);group[key].append(dict(row,source_line=line,semantic_message=msg))
  byside[side]=(d,group)
 details=[];new=removed=inherited=0;changed=[]
 for key in sorted(set(byside['BASE'][1])|set(byside['HEAD'][1])):
  a=byside['BASE'][1].get(key,[]);b=byside['HEAD'][1].get(key,[]);common=min(len(a),len(b));new+=max(0,len(b)-len(a));removed+=max(0,len(a)-len(b));inherited+=common;r={'identity':{'path':key[0],'level':key[1],'message_with_only_source_positions_and_dynamic_line_counts_normalized':key[2]},'BASE':a,'HEAD':b,'BASE_count':len(a),'HEAD_count':len(b),'inherited_count':common,'new_count':max(0,len(b)-len(a)),'removed_count':max(0,len(a)-len(b)),'raw_rows_equal':a==b};details.append(r)
  if a!=b:changed.append(r)
 levels=lambda d:dict(collections.Counter(r.get('level','FINDING') for r in d['findings']));summary[kind]={'BASE_exit':byside['BASE'][0]['exit'],'HEAD_exit':byside['HEAD'][0]['exit'],'BASE_findings':len(byside['BASE'][0]['findings']),'HEAD_findings':len(byside['HEAD'][0]['findings']),'BASE_levels':levels(byside['BASE'][0]),'HEAD_levels':levels(byside['HEAD'][0]),'new_identity_occurrences':new,'removed_identity_occurrences':removed,'inherited_identity_occurrences':inherited,'identities_with_changed_raw_messages_or_positions':len(changed),'normalization':'Only source line locations and dynamic source/proof line counts. No definition-name lists, severity, declaration-name or semantic-message normalization. Full raw messages/positions retained for every identity.'};(O/(kind+'-identity-dispositions.json')).write_text(json.dumps(details,indent=2)+'\n')
 a=(O/('BASE-'+kind+'.txt')).read_text();b=(O/('HEAD-'+kind+'.txt')).read_text();(O/(kind+'.txt.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile='BASE-'+kind,tofile='HEAD-'+kind)))
A=json.loads((O/'BASE-size.txt').read_text());B=json.loads((O/'HEAD-size.txt').read_text());sizes=[]
for a,b in zip(A,B):
 assert a['path']==b['path'];sizes.append({'path':a['path'],'BASE':a,'HEAD':b,'delta_bytes':b['bytes']-a['bytes'],'delta_lines':b['lines_splitlines']-a['lines_splitlines'],'crossed1000':a['over1000_splitlines']!=b['over1000_splitlines'],'crossed600':a['over600_splitlines']!=b['over600_splitlines']})
summary['sizes']={'BASE_bytes':sum(r['bytes'] for r in A),'HEAD_bytes':sum(r['bytes'] for r in B),'BASE_lines':sum(r['lines_splitlines'] for r in A),'HEAD_lines':sum(r['lines_splitlines'] for r in B),'BASE_over1000':sum(r['over1000_splitlines'] for r in A),'HEAD_over1000':sum(r['over1000_splitlines'] for r in B),'crossed1000_files':[r['path'] for r in sizes if r['crossed1000']],'crossed600_files':[r['path'] for r in sizes if r['crossed600']]};(O/'size-dispositions.json').write_text(json.dumps(sizes,indent=2)+'\n');(O/'comparison.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
