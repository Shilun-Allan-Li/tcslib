"""Create a complete replayable series and verify every commit and changed source byte."""
from pathlib import Path
import subprocess,os,csv,sys
n,rev=sys.argv[1:3]
base='107f1e8c218733eac12d6b9bee6fece441271317'
repo=Path.cwd(); out=repo/'evidence'/f'checkpoint{n}-patches'
assert not out.exists(),out
out.mkdir()
def run(args,**kw):
 print('+', ' '.join(map(str,args)),flush=True)
 p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,**kw)
 print(p.stdout,end='',flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 return p.stdout.strip()
commits=subprocess.check_output(['git','rev-list','--reverse',base+'..'+rev],text=True).splitlines()
patches=run(['git','format-patch','--no-signature','--output-directory',str(out),base+'..'+rev]).splitlines()
rows=[]
for h in commits:
 vals=subprocess.check_output(['git','show','-s','--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI',h],text=True).rstrip('\n').split('\t')
 raw=subprocess.check_output(['git','cat-file','commit',h],text=True)
 assert '\ngpgsig ' not in raw
 rows.append(vals+['unsigned; commit.gpgsign=false'])
with (out/'COMMITS.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n')
 w.writerow(['commit','author_name','author_email','author_date','committer_name','committer_email','committer_date','signing']);w.writerows(rows)
scratch=Path('/private/tmp')/f'seq-zk-replay-cp{n}'
assert not scratch.exists(),scratch
run(['git','clone','--shared','--no-checkout',str(repo),str(scratch)])
run(['git','checkout','--detach',base],cwd=scratch)
for row,patch in zip(rows,patches,strict=True):
 env=dict(os.environ,GIT_COMMITTER_NAME=row[4],GIT_COMMITTER_EMAIL=row[5],GIT_COMMITTER_DATE=row[6])
 run(['git','-c','commit.gpgsign=false','am',patch],cwd=scratch,env=env)
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=scratch,text=True).strip()
 assert actual==row[0],(actual,row[0]);print('EXACT COMMIT',actual,flush=True)
paths=subprocess.check_output(['git','diff','--name-only',base,rev],text=True).splitlines()
for path in paths:
 expected=subprocess.check_output(['git','show',rev+':'+path])
 assert (scratch/path).read_bytes()==expected,path
 print('SOURCE-BYTES EXACT',path,flush=True)
print('REPLAY PASS:',len(rows),'commits;',len(paths),'source files;',rev,flush=True)
