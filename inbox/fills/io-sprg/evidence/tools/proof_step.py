# io-sprg one-body sorry ladder, Mac host 2026-11-18. Root only; no Lean.
# Preserves the existing declaration statement and docstring; archives each replacement.
import argparse,datetime,hashlib,json,re,subprocess
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('file');ap.add_argument('name');ap.add_argument('body');a=ap.parse_args();root=Path.cwd()
freeze=root/'evidence/freeze/M0.txt';assert freeze.exists(),'M0 must be frozen and delivered before proof filling'
frozen=freeze.read_text().strip();subprocess.run(['git','merge-base','--is-ancestor',frozen,'HEAD'],check=True)
p=root/a.file;assert str(p.relative_to(root)).startswith('TCSlib/Cryptography/Obfuscation/') and p.suffix=='.lean'
source=p.read_text();name=re.escape(a.name)
starts=list(re.finditer(r'^(?:private |protected )?(?:theorem|lemma) '+name+r'(?=\s|\{|\(|:)',source,re.M));assert len(starts)==1,(a.name,len(starts))
start=starts[0].start();tail=source[start:];match=re.search(r':=\s+(?:sorry\b|by\s*\n\s*sorry\b)',tail);assert match,'The existing body must be one M0 sorry stub'
body=Path(a.body).read_text().strip();assert body.startswith('by\n') or not re.search(r'\bby\b',body)
assert len(re.findall(r'\bby\b',body))<=1,'At most one new tactic block per invocation'
assert not re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',body),'Only complete candidate bodies are inserted by this tool'
assignment_start=start+match.start();body_start=assignment_start+2;body_end=start+match.end()
assert ':=' not in source[start:assignment_start],'Unexpected declaration syntax; inspect manually'
new=(source[:assignment_start]+':= '+body+source[body_end:] if body.startswith('by\n') else source[:body_start].rstrip()+'\n  '+body+source[body_end:])
assert max(map(len,new.splitlines()),default=0)<=100 and len(new.splitlines())<=1000
steps=root/'evidence/steps';steps.mkdir(exist_ok=True);n=1+max([int(x.name) for x in steps.iterdir() if x.is_dir() and x.name.isdigit()] or [0]);folder=steps/f'{n:03d}';folder.mkdir()
(folder/'before.lean.txt').write_text(source);(folder/'candidate.proof').write_text(body+'\n')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(folder/'step.json').write_text(json.dumps(dict(file=a.file,name=a.name,m0=frozen,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_before_sha256=sha(source),source_after_sha256=sha(new),body_sha256=sha(body),status='INSERTED_NOT_CHECKED'),indent=1)+'\n')
p.write_text(new);print('INSERTED_ONE_BODY',a.name,'step',n)
