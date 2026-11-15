"""Final frozen headers, permitted paths, exact source widths and lint line-set audit."""
from pathlib import Path
import subprocess,json,re,collections,hashlib,csv
B='107f1e8c218733eac12d6b9bee6fece441271317';R='d842dc8f681f6b89499129f5b64a50d0e4587935';E=Path('evidence')
def git(*args):return subprocess.check_output(['git',*args],text=True)
assert git('rev-parse','HEAD').strip()==R
paths=git('diff','--name-only',B,R).splitlines();main='TCSlib/Cryptography/Composability/SequentialZK.lean';defs='TCSlib/Cryptography/ZeroKnowledge/Defs.lean'
assert len(paths)==41 and all(p in [main,defs] or p.startswith('TCSlib/Cryptography/Composability/SequentialZK/') for p in paths)
assert not git('diff','HEAD','--','TCSlib');assert not git('ls-files','--others','--exclude-standard','TCSlib')
inventory=[]
for p in paths:
 raw=Path(p).read_bytes();assert raw==subprocess.check_output(['git','show',R+':'+p]);ls=raw.decode().splitlines();assert len(ls)<=1000 and max(map(len,ls))<=100
 inventory.append(dict(path=p,lines=len(ls),max_width=max(map(len,ls)),sha256=hashlib.sha256(raw).hexdigest()))
new=git('diff','--unified=0',B,R,'--','TCSlib');assert not re.search(r'^\+(?:\s*@\[[^\]]*\bsimp\b|\s*attribute\s+\[[^\]]*\bsimp\b)',new,re.M), 'Review new simp attribute or syntax'
def headers(t):
 return {m[1]:m[0] for m in re.finditer(r'theorem ((?:ZK|StatZK|InteractiveProof|InteractiveProofErr|EfficientProverProofErr)\.seqRep)\b[\s\S]*?:= by',t)}
a=headers(git('show',B+':'+main));b=headers(git('show',R+':'+main));assert len(a)==5 and a==b,(a.keys(),b.keys())
base=Path('evidence/logs/lint-base.log').read_text().splitlines();fin=Path('evidence/logs/lint-final-repair.log').read_text().splitlines();base={s for s in base if s.startswith(('FAIL ','WARN '))};fin={s for s in fin if s.startswith(('FAIL ','WARN '))};added=sorted(fin-base);removed=sorted(base-fin);assert not any(s.startswith('FAIL ') for s in added);assert len(added)==len(removed)==1 and 'StatZK' in removed[0] and '2 public def(s)' in added[0]
summary=dict(revision=R,files=len(paths),helpers=39,total_lines=sum(r['lines'] for r in inventory),main_lines=next(r['lines'] for r in inventory if r['path']==main),max_file_lines=max(r['lines'] for r in inventory),max_width=max(r['max_width'] for r in inventory),five_frozen_headers_identical=True,only_approved_frozen_reader=True,no_new_global_simp_attribute=True,lint_base=dict(collections.Counter(s.split()[0] for s in base)),lint_final=dict(collections.Counter(s.split()[0] for s in fin)),new_fail_lines=0,added_warn_lines=added,removed_warn_lines=removed)
(E/'final-source-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n');(E/'logs/final-static-audit.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
