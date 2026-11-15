from pathlib import Path
import re,json,hashlib
root=Path('/Users/seyoonr/.codex/worktrees/seq-zk-proof/tcslib-exchange')
base=Path('evidence/subagents/seq-zk-a')
files=[l.strip()+'.lean' for l in (root/'evidence/final-helper-order-01.txt').read_text().splitlines() if l.strip()]
pat=re.compile(r'^(?P<private>private\s+)?(?:(?:noncomputable|unsafe|partial|protected)\s+)*(?P<kind>def|abbrev|theorem|lemma|structure|class|instance)\s+(?P<name>[^\s({:]+)')
records=[];hashes={};source_info=[]
for file in files:
 text=(root/file).read_text();lines=text.splitlines();hashes[file]=hashlib.sha256(text.encode()).hexdigest()
 source_info.append({'file':file,'lines':len(lines),'max_width':max(map(len,lines)),'module_refs':'## References' in text,'global_simp_attribute':bool(re.search(r'@\[simp(?:\s|\])|attribute\s+\[simp\]',text))})
 starts=[(i,m) for i,l in enumerate(lines) if(m:=pat.match(l))];names={m.group('name') for _,m in starts}
 for ix,(i,m) in enumerate(starts):
  stop=starts[ix+1][0] if ix+1<len(starts) else len(lines)
  prefix='\n'.join(lines[:i]);docs=list(re.finditer(r'/--[\s\S]*?-/',prefix));doc='';docline=None
  if docs:
   d=docs[-1]
   if not re.sub(r'@\[[\s\S]*?\]','',prefix[d.end():]).strip():doc=d.group();docline=prefix[:d.start()].count('\n')+1
  region='\n'.join(lines[i:stop]);p=re.search(r':=\s*by\b',region);proof=''
  if p:proof=re.split(r'\n(?=/--|namespace\b|end\b|section\b)',region[p.end():],maxsplit=1)[0].rstrip()
  records.append({'file':file,'line':i+1,'kind':m.group('kind'),'name':m.group('name'),'private':bool(m.group('private')),'doc':doc,'docline':docline,'proof_lines':len(proof.splitlines()) if proof else 0,'proof_nonblank_lines':sum(bool(x.strip()) for x in proof.splitlines()),'sketch':'**Proof sketch.**' in doc,'proof_comments':len(re.findall(r'^\s*--',proof,re.M)),'literal_readers':[x for x in [m.group('name')+'_eq',m.group('name')+'_iff'] if x in names],'simps_attr':'simps' in prefix[-200:],'region':region})
(base/'final11-source-audit-inventory.json').write_text(json.dumps({'source_order':files,'source_sha256':hashes,'source_info':source_info,'declarations':records},indent=2)+'\n')
print('Files',len(files),'declarations',len(records))
print('File size/width/reference/simp findings:')
for s in source_info:
 if s['lines']>1000 or s['max_width']>100 or not s['module_refs'] or s['global_simp_attribute']:print(s)
print('Missing docs:')
for r in records:
 if not r['private'] and r['kind']!='instance' and not r['doc']:print(r['file'],r['line'],r['name'])
print('Public def/abbrev readers:')
for r in records:
 if not r['private'] and r['kind'] in ['def','abbrev']:print(r['file'],r['line'],r['name'],r['literal_readers'],r['simps_attr'])
print('Proofs>=15 without sketches:')
for r in records:
 if r['proof_lines']>=15 and not r['sketch']:print(r['file'],r['line'],r['name'],r['proof_lines'])
print('Proofs>=25 without step comments:')
for r in records:
 if r['proof_lines']>=25 and not r['proof_comments']:print(r['file'],r['line'],r['name'],r['proof_lines'])
print('All proofs>=15:')
for r in records:
 if r['proof_lines']>=15:print(r['file'],r['line'],r['name'],r['proof_lines'],r['sketch'],r['proof_comments'])
