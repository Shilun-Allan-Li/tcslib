from pathlib import Path
import os,json,subprocess,datetime,time,hashlib,re,sys
O=Path('/private/tmp/ab34-fe-live1-final-validation');E=O/'evidence';F=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);P=O/'live/metadata-project';probe=P/'Inventory.lean';summary=json.loads((E/'REPLAY-SUMMARY.json').read_text());assert summary['PASS'];rows=[]
for label,ol in [('BASE',S/'oleans-mac8'),('HEAD',O/'live/oleans-fe1')]:
 out=E/'metadata';out.mkdir(exist_ok=True);argv=['bash',str(F/'devtools/seyoon/leanelab.sh'),str(P),str(ol),str(probe)];start=datetime.datetime.now(datetime.timezone.utc).isoformat();tm=time.monotonic();r=subprocess.run(argv,cwd=P,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=r.stdout;(out/(label+'.out')).write_bytes(raw);errors=len(re.findall(r': error(?:\([^\n]*?\))?:',raw.decode(errors='replace')));d={'label':label,'argv':argv,'start_utc':start,'seconds':time.monotonic()-tm,'exit':r.returncode,'errors':errors,'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'input_sha256':hashlib.sha256(probe.read_bytes()).hexdigest(),'output_bytes':len(raw),'output_sha256':hashlib.sha256(raw).hexdigest(),'whole_snapshot':str(ol),'one_own_Lean_at_a_time':True,'compiled_declarations_not_source_reelaboration':True,'proof_values_not_rendered':True};(out/(label+'-run.json')).write_text(json.dumps(d,indent=2)+'\n');rows.append(d);print(json.dumps(d),flush=True)
 if r.returncode or errors:sys.exit(1)
 parsed=[];complete=[]
 for line in raw.decode().splitlines():
  if 'META|' in line:parsed.append(json.loads(line.split('META|',1)[1]))
  if 'COMPLETE|' in line:complete.append(line.split('COMPLETE|',1)[1])
 assert len(complete)==1 and int(complete[0].split('|')[0])==len(parsed) and parsed
 assert len({x['name'] for x in parsed})==len(parsed)
 (out/(label+'.json')).write_text(json.dumps(parsed,indent=2)+'\n');print(label+' metadata records='+str(len(parsed)),flush=True)
(E/'metadata/RUNS.json').write_text(json.dumps(rows,indent=2)+'\n')
