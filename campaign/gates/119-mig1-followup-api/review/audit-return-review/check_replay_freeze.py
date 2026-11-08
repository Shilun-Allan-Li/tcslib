from pathlib import Path
import collections,hashlib,json,re,subprocess
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=R/'campaign/gates/119-mig1-followup-api';OUT=G/'review/audit-return-review';P=G/'evidence/replay-mfup2'
order=[x for x in (P/'down-mfup2.txt').read_text().splitlines() if x.strip()];log=(P/'replay-mfup2.log').read_text();launch=(P/'replay-mfup2-launches.log').read_text();rows=re.findall(r'^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',log,re.M);assert [r[0] for r in rows]==order and len(rows)==401;assert all(r[1]=='0' and r[2]=='0' for r in rows);assert sum(int(r[3]) for r in rows)==77
launches=re.findall(r'^pid=(\d+) -j4 (\S+)\.lean -o (\S+)\.olean$',launch,re.M);assert len(launches)==401 and [x[1] for x in launches]==order;assert all(x[2].endswith('/oleans-mfup2/'+module) for x,module in zip(launches,order));assert len({x[0] for x in launches})==401
static=(P/'replay-mfup2-static.txt').read_text();assert 'mismatches=0' in static or 'mismatches 0' in static or 'mismatches: 0' in static,static
(OUT/'replay-complete-row-check.json').write_text(json.dumps(dict(ordered_unique_modules=401,all401_exit_error_rows_zero=True,all401_exact_effective_j4_launches_in_order=True,sum_native_sorries=77,static_raw=static,no_new_replay_or_snapshot_content_check=True),indent=2)+'\n')
freeze=json.loads((G/'source/whole-source-freeze.json').read_text());data=[];base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';head='f1ca767a10551960faf36ad9c8ff17bea3a2d88c'
for row in freeze['source_scope']:
 path=row['path'];a=subprocess.run(['git','-C',str(R),'show',base+':'+path],stdout=subprocess.PIPE,check=True).stdout;b=subprocess.run(['git','-C',str(R),'show',head+':'+path],stdout=subprocess.PIPE,check=True).stdout;assert hashlib.sha256(a).hexdigest()==row['before_sha256'] and hashlib.sha256(b).hexdigest()==row['after_sha256']
 i=0
 while i<min(len(a),len(b)) and a[i]==b[i]:i+=1
 if len(b)>len(a):
  n=len(b)-len(a);assert b[:i]+b[i+n:]==a;kind='one exact insertion'
 else:
  n=len(a)-len(b);assert a[:i]+a[i+n:]==b;kind='one exact deletion'
 data.append(dict(path=path,kind=kind,byte_delta=len(b)-len(a),every_other_original_byte_recovered=True))
block=(G/'source/approved-moved-block.lean.txt').read_bytes();assert len(block)==1043 and hashlib.sha256(block).hexdigest()=='3de684d6d30b02098aaf68c8b4223d9d8c92e2ff037505fdd3b5f494412baedf'
(OUT/'source-freeze-crosscheck.json').write_text(json.dumps(dict(files=data,five_source_hashes_exact=True,approved_redirect_block_bytes=1043,approved_redirect_block_sha256=hashlib.sha256(block).hexdigest()),indent=2)+'\n');(OUT/'check_replay_freeze.py').write_bytes(Path(__file__).read_bytes());print('401 exact pass/launch rows,77sorries, five whole-file single-splice recovery checks and1043-byte adopted block verified.')
