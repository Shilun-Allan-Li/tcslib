from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys,time
O=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup/review/round3-image-repoint')
C=json.loads((O/'context.json').read_text());name=sys.argv[1]
assert re.fullmatch('[A-Za-z0-9_-]+',name)
src=O/(name+'.lean.txt'); log=O/(name+'.out'); receipt=O/(name+'-run.json')
assert not log.exists() and not receipt.exists()
b=src.read_bytes();p=Path(C['scratch'])/(name.replace('-','_')+'.lean');p.write_bytes(b)
command=['bash',str(Path(C['records'])/'devtools/seyoon/leanelab.sh'),C['worktree'],C['snapshot'],str(p)]
start=time.time();row={'command':command,'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'input_sha256':hashlib.sha256(b).hexdigest(),'local_slots':os.environ.get('TCSLIB_LEAN_SLOTS'),'plain_managed':True,'no_outer_lock':True,'no_compiled_output':True}
(O/(name+'-request.json')).write_text(json.dumps(row,indent=2)+'\n')
with log.open('wb') as f:
    result=subprocess.run(command,cwd=C['records'],stdout=f,stderr=subprocess.STDOUT)
data=log.read_bytes();text=data.decode('utf-8')
row.update(exit=result.returncode,seconds=time.time()-start,errors=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',text,re.M)),output_sha256=hashlib.sha256(data).hexdigest(),output_bytes=len(data))
receipt.write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(row,indent=2))
print('\n'.join(line for line in text.splitlines() if ' error' in line or line.startswith(('ROOT|','PROOFAX|','FOREIGNDEF|','HOMEDEF|','CITED|'))))
