from pathlib import Path
import json,hashlib,subprocess,re,datetime,collections,base64,tarfile,io
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');L=R/'campaign/fills/f6/landing';O=Path('/private/tmp/f6-gate120-peer-review');S='0d0950caeb39300b5cc9bf41e5f07392fb26d3e5';B='3023dc1408c3d216fc07a7cbba9ae30135b861ed';OLD='f72a807e2376a2b986675c992745d6affc23b96f';REL='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def blob(pin,path):return git('show',pin+':'+path)
def j(p):return json.loads(p.read_bytes())
# Verify every artifact of each explicitly frozen input, without touching caches or running scripts.
manifest_checks=[]
for sub,wanted in [('compiled-accounting-final','0c8d3487e95c62731d750f2b91f1a93314b64861bffced766d5389885e2faad9'),('source-screen23-resumed','9412b0d8bcdbb4dd28583069c78100e22f7abf69316ec2a5c6292364e815329a'),('source-screen23-resumed/final23-current','2b0c6cf93595fef48fe5bc9eac9ee911e521f309bb4ed831aa4256ad34062f2c'),('seam-step-repoint-applied','318e85633bb50630d9c6f633f6907eb74da5faa7e3f490427c24e60cb2a99671'),('replay-mf61',None),('replay-mf62',None)]:
 p=L/sub;raw=(p/'MANIFEST.json').read_bytes();h=sha(raw);assert wanted is None or h==wanted,(sub,h,wanted);m=json.loads(raw)
 for row in m['files']:
  b=(p/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],(sub,row['path'])
 for ln in (p/'SHA256SUMS').read_text().splitlines():
  h0,name=ln.split(None,1);assert sha((p/name.lstrip('* ')).read_bytes())==h0,(sub,name)
 manifest_checks.append({'path':str((p/'MANIFEST.json').relative_to(R)),'sha256':h,'declared_artifacts':len(m['files']),'all_artifact_and_checksum_bytes_exact':True})
for pin in [S,B,OLD]:assert git('rev-parse',pin+'^{commit}').decode().strip()==pin;git('cat-file','-e',pin+'^{commit}')
assert git('diff','--name-only',B,S,'--','*.lean').decode().splitlines()==[REL]
head=blob(S,REL);base=blob(B,REL);assert sha(head)=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3';assert head==(L/'compiled-accounting-final/Hierarchy-head.lean.txt').read_bytes();assert base==(L/'compiled-accounting-final/Hierarchy-base.lean.txt').read_bytes()
hs=head.index(b'theorem space_universal :');he=head.index(b':=',hs);bs=base.index(b'theorem space_universal :');be=base.index(b':=',bs);assert head[hs:he]==base[bs:be]==(R/'campaign/fills/f6/issue-preparation/inputs/space_universal-header.txt').read_bytes();assert sha(head[hs:he])=='89d2609a76de64f38283e2d9cf7338791aa451a7e08a46fb02f07eb182f5f62f'
# The target is the first baseline declaration; all pre-existing following source bytes are exact.
tail=b'/-- The inclusion half: `hfg` at `A = 1`';assert head[head.index(tail):]==base[base.index(tail):]
D=L/'source-screen23-resumed/final23-current';chunks=j(D/'new19-complete-headers-and-chunks.json');assert len(chunks)==19;scope=[]
for q in chunks:
 text=q['raw_text'];assert text in head.decode();start=head.decode().index(text);line=head.decode().count('\n',0,start)+1;assert line==q['start_line'];assert q['private']==(q['name']!='Complexity.space_universal')
 scope.append({'name':q['name'],'line':line,'private':q['private'],'complete_chunk_SHA256':sha(text.encode()),'complete_raw_chunk_exact':True,'body_lines':q['body_lines']})
assert len({q['name'] for q in chunks})==19
# Every complete old import is unchanged, and the target/new helpers are the only source deltas.
imports=lambda b:re.findall(rb'^import .+$',b,re.M);assert imports(head)==imports(base)
# Raw screen row reconciliation and all46 full sources/archives.
pop=(D/'population.txt').read_text().splitlines();old21=(D/'issued21-population.txt').read_text().splitlines();assert len(pop)==23 and len(old21)==21 and set(pop)-set(old21)=={'TCSlib/Complexity/SpaceComplexity/Inclusions.lean','TCSlib/Complexity/SpaceComplexity/ConfigCount.lean'}
screens={};cm={}
for ep,pin,expect in [('base',B,(1113,647,172081)),('head',S,(1124,648,172243))]:
 for f in pop:assert (D/'inputs'/ep/(f+'.txt')).read_bytes()==blob(pin,f)
 ix=j(D/(ep+'-index.json'));im={x['label']:x for x in ix};assert len(im)==len(ix)
 for x in ix:assert len(x['normalized_body'])==x['body_chars']
 raw=(D/(ep+'.out')).read_text();rows=[]
 for ln in raw.splitlines()[1:]:
  m=re.fullmatch(r'\s+(\S+)  reproduces  (\S+): (\d+)/(\d+) = (\d+)%',ln);assert m;aa,bb,ss,dd,pp=m.groups();assert im[bb]['body_chars']==int(dd);rows.append((aa,bb,int(ss),int(dd),int(pp)))
 assert rows==[(x['a'],x['b'],x['shared'],x['denominator'],x['printed_percent']) for x in j(D/(ep+'-candidates.json'))];assert (len(ix),len(rows),sum(x[2] for x in rows))==expect
 archive=base64.b64decode(b''.join((D/(ep+'.tar.base64.txt')).read_bytes().split()),validate=True)
 with tarfile.open(fileobj=io.BytesIO(archive),mode='r:*') as tf:
  fs=[x for x in tf.getmembers() if x.isfile()];assert len(fs)==23
  for x in fs:assert x.name in pop and tf.extractfile(x).read()==blob(pin,x.name)
 cm[ep]={(x[0],x[1]):x[2:] for x in rows};screens[ep]={'eligible':len(ix),'candidates':len(rows),'shared_chars':sum(x[2] for x in rows),'all23_source_captures_and_archive_entries_exact':True}
added=cm['head'].keys()-cm['base'].keys();assert len(added)==1 and not cm['base'].keys()-cm['head'].keys();assert all(cm['base'][k]==cm['head'][k] for k in cm['base']);edge=next(iter(added));assert edge==('Hierarchy.lean::f6_native_halt','UniversalK.lean::ss_inputRewind_done') and cm['head'][edge]==(162,321,50)
for q in j(D/'new-E3-comparison.json')['complete_compared_chunks']:
 raw=blob(S,q['path']).decode();assert q['complete_raw_chunk'] in raw and sha(q['complete_raw_chunk'].encode())==q['sha256']
# Two distinct actual replay generations and exact launched populations, not a relabeled final229 run.
replays=[]
for label,pin,count,total in [('mf61',OLD,229,21),('mf62',S,2,0)]:
 p=L/('replay-'+label);r=j(p/'receipt.json');assert r['head']==pin and r['pipeline_exit']==r['failed']==r['error_rows']==0 and r['modules']==count and r['static_total']==total
 log=(p/('replay-'+label+'.log')).read_text();rows=re.findall(r'^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',log,re.M);order=(p/('order-'+label+'.txt')).read_text().splitlines();assert len(rows)==len(set(x[0] for x in rows))==count and [x[0] for x in rows]==order
 assert all(x[1:3]==('0','0') for x in rows) and sum(int(x[3]) for x in rows)==total
 launches=[]
 for ln in (p/('replay-'+label+'-launches.log')).read_text().splitlines():
  m=re.fullmatch(r'pid=\d+ (?:-j4 )+(\S+)\.lean -o (\S+)\.olean',ln);assert m and m[2].endswith('/oleans-'+label+'/'+m[1]);launches.append(m[1])
 assert launches==order
 assert (p/('replay-'+label+'-static.txt')).read_text()==f'modules {count}, mismatches 0, static total {total}\n'
 replays.append({'label':label,'head':pin,'rows':count,'distinct_effective_j4_launches':count,'failures':0,'errors':0,'static_total':total})
objs=j(L/'replay-mf62/snapshot-object-comparison.json');assert len(objs['input'])==len(objs['output'])==895 and set(objs['input'])==set(objs['output']);changed=[n for n in objs['input'] if objs['input'][n]!=objs['output'][n]];assert changed==['TCSlib/Complexity/SpaceComplexity/Hierarchy.olean'];assert objs['output'][changed[0]]['sha256']==j(L/'compiled-accounting-final/context.json')['owner_olean_sha256']
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':S,'base':B,'manifest_checks':manifest_checks,'target_header_bytes':he-hs,'target_header_SHA256':sha(head[hs:he]),'old_following_source_and_imports_byte_frozen':True,'new19_exact_chunks':scope,'screens':screens,'new_E3_edge':{'a':edge[0],'b':edge[1],'shared_denominator_percent':cm['head'][edge]},'replays':replays,'whole895_context_transition_only_Hierarchy_changed':True,'native2_Hierarchy_matches_MF62_object':True,'no_Lean_screens_supplied_scripts_or_snapshot_actions':True}
(O/'foundation-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['new19_exact_chunks','manifest_checks']},indent=2))
