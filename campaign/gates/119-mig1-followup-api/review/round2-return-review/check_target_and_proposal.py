from pathlib import Path
import json,re,hashlib,subprocess,collections
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=R/'campaign/gates/119-mig1-followup-api';O=Path('/private/tmp/gate119-round2-return-review')
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_bytes())
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
runs=[]
for dirname,stems in [('first-entry',['Actual-module','Finite-newsection-sealed']),('pair-diag',['Owner-native','Owner-sealed']),('inc-redirect',['Primitives-native-v2','Primitives-sealed-v2','Wrappers-native-v2','Wrappers-sealed-v2','Published-consumers','Raw-header-boundary','Primitives-native','Primitives-sealed','Wrappers-native','Wrappers-sealed'])]:
 d=G/'review'/dirname
 for stem in stems:
  rc=j(d/(stem+'-run.json'));src=d/('actual-Finite.lean.txt' if stem=='Actual-module' else stem+'.lean.txt');out=(d/(stem+'.out')).read_bytes()
  assert sha(src.read_bytes())==rc['input_sha256'] and sha(out)==rc['output_sha256'];text=out.decode();err=len(re.findall(r':\d+:\d+: error:',text))
  assert err==rc['errors']
  expected_bad=stem in ['Raw-header-boundary','Primitives-native','Primitives-sealed','Wrappers-native','Wrappers-sealed']
  assert (rc['exit'],err)==((1,1) if expected_bad else (0,0))
  if stem=='Raw-header-boundary':assert 'Fin M.k' in text and 'Fin (M.redirectTM haltOn).k' in text
  elif expected_bad:assert 'olean' in text and 'incompatible' in text
  runs.append({'group':dirname,'name':stem,'exit':rc['exit'],'errors':err,'input_sha256':rc['input_sha256'],'output_sha256':rc['output_sha256'],'role':'retained toolchain setup failure' if expected_bad and stem!='Raw-header-boundary' else 'expected opaque raw-header boundary' if stem=='Raw-header-boundary' else 'supplied passing native/sealed/consumer check'})
# All previous findings and resolutions are present, verbatim, and keyed one-to-one.
f=(G/'findings.md').read_bytes();copy=(G/'review/audit-return-review/findings.received.md').read_bytes();assert f==copy and len(f)==16515 and sha(f)=='663dda3e98a0dca66162492f7319996babb2ec815159980a1e62bde6cda8a0c4'
res=(G/'resolutions.md').read_text();rows=re.findall(r'^\| ([0-9]+) \| (major|note) \| (.+) \|$',res,re.M);assert [int(i[0]) for i in rows]==list(range(1,18));assert rows[0][1]=='major' and all(i[1]=='note' for i in rows[1:])
# The by-kind scope/owner/window is a recorded human decision, not this review's decision.
ruling=j(G/'ruling-live-stop.json');assert ruling['user_answer']=='Accept this scheduled debt (Recommended)' and ruling['family']=='FE-LIVE-1' and ruling['owner']=='maintainer(Codex)'
assert ruling['window']=='Staged MIG conversions in #233 before gate118; remaining existing instances in next12.2c consolidation after active MIG-1 and before further SAT/Hardness fills.'
assert ruling['finding_sha256']==sha(f) and ruling['source']=='f1ca767a10551960faf36ad9c8ff17bea3a2d88c'
# Decode the definitive proposal as a patch in memory, without executing Git apply or delivered scripts.
p=R/'campaign/fills/mig1/landing/followup119-consumer-proposal';rc=j(p/'generation2/receipt.json');patch=(p/'generation2/all15-bodies.patch').read_text();pin=git('rev-parse',rc['baseline']+'^{commit}').decode().strip();git('cat-file','-e',pin+'^{commit}')
lines=patch.splitlines(keepends=True);i=0;files=[];hunks=0
while i<len(lines):
 if not lines[i].startswith('--- a/'):
  i+=1;continue
 path=lines[i][6:].strip();assert lines[i+1]=='+++ b/'+path+'\n';i+=2
 before=git('show',pin+':'+path);old=before.decode().splitlines(keepends=True);out=[];pos=0;fh=0
 while i<len(lines) and not lines[i].startswith(('--- a/','diff --git ')):
  if not lines[i].startswith('@@ '):i+=1;continue
  m=re.match(r'@@ -([0-9]+)(?:,([0-9]+))? \+([0-9]+)(?:,([0-9]+))? @@',lines[i]);assert m
  oldstart=int(m[1])-1;oldcount=int(m[2] or 1);newcount=int(m[4] or 1);i+=1;a=[];b=[]
  while i<len(lines) and not lines[i].startswith(('@@ ','--- a/','diff --git ')):
   ln=lines[i]
   if ln.startswith(' '):a.append(ln[1:]);b.append(ln[1:])
   elif ln.startswith('-'):a.append(ln[1:])
   elif ln.startswith('+'):b.append(ln[1:])
   elif ln.startswith('\\ No newline'):raise AssertionError('Unexpected missing final LF')
   else:break
   i+=1
  assert len(a)==oldcount and len(b)==newcount,(path,len(a),oldcount,len(b),newcount)
  assert old[oldstart:oldstart+oldcount]==a and oldstart>=pos
  out.extend(old[pos:oldstart]);out.extend(b);pos=oldstart+oldcount;hunks+=1;fh+=1
 out.extend(old[pos:]);after=''.join(out).encode();meta=next(x for x in rc['files'] if x['file']==path)
 assert (len(before),sha(before),len(after),sha(after))==(meta['bytes_before'],meta['before_sha256'],meta['bytes_after'],meta['after_sha256'])
 files.append({'path':path,'hunks':fh,'before_sha256':sha(before),'after_sha256':sha(after),'in_memory_patch_matches_receipt':True})
assert len(files)==6 and rc['changes_count']==len(rc['changes'])==15 and rc['least_entry_sites']==12
assert collections.Counter(x['kind'] for x in rc['changes'])=={'generation1_reuse':5,'existing_NONE_first_halt':7,'API119_inline_live_stop':2,'API119_exact_owner_adoption':1},collections.Counter(x['kind'] for x in rc['changes'])
# Authenticate bounded proposal's original five-root and14-control evidence as data.
prop_runs=[]
for stem in ['Consumers-native','Consumers-sealed','Controls-native','Controls-sealed']:
 rr=j(p/(stem+'-run.json'));src=(p/(stem+'.lean.txt')).read_bytes();raw=(p/(stem+'.out')).read_bytes();assert sha(src)==rr['input_sha256'] and sha(raw)==rr['output_sha256'];prop_runs.append({'name':stem,'exit':rr['exit'],'errors':rr['errors']})
assert [(x['exit'],x['errors']) for x in prop_runs]==[(0,0),(0,0),(0,0),(1,14)]
out={'target_execution_receipts':runs,'prior_findings':{'bytes':len(f),'sha256':sha(f),'copies_identical':True,'all17_resolution_rows_present':True},'ruling':ruling,'proposal':{'baseline':pin,'files':files,'hunks':hunks,'declared_changes':15,'least_entry_changes':12,'gen2_NOT_elaborated_by_review':True,'bounded_gen1_runs':prop_runs},'canonical_round2_closure_update_remaining_for_parent':True}
(O/'target-proposal-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='target_execution_receipts'},indent=2))
