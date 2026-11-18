"""PHFE static boundary, scope, and admission inventory; no Lean invocations."""
from pathlib import Path
import re,subprocess,json,hashlib,datetime,importlib.util,sys
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('pinned_lexer','evidence/preparation/tools/seal/review/archived-gate10-tools/scan_explicit.py');lexer=importlib.util.module_from_spec(spec);spec.loader.exec_module(lexer)
base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb';out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
files=Path('evidence/logs/owned-files.txt').read_text().splitlines()
checks={k:[] for k in ['forbidden_import','contract_import_location','local_contract','local_realizesOn','forbidden_admission','sampler_instance','bare_nonuniform_efficiency','rdlog','new_axiom','namespace']};admissions=[];lines=[]
for f in files:
 s=Path(f).read_text();mask=lexer.blank(s);lines.append((f,len(s.splitlines()),max(map(len,s.splitlines()),default=0),hashlib.sha256(s.encode()).hexdigest()))
 for i,(a,b) in enumerate(zip(s.splitlines(),mask.splitlines()),1):
  if re.search(r'^import (TCSlib\.(Programs|Complexity\.RAMSimulation)|TCSlib\.Cryptography\.Games\.Closeness)',b):checks['forbidden_import'].append((f,i,a))
  if re.search(r'^import TCSlib\.Cryptography\.CoinSampling\.',b):
   if not re.search(r'^import TCSlib\.Cryptography\.CoinSampling\.(Contract|Efficiency)$',b):checks['forbidden_import'].append((f,i,a))
   if not any(t in f for t in ['/Defs/','/SemiAdaptive/','/PartialGarbling/','/Wee20/Targets/']):checks['contract_import_location'].append((f,i,a))
  if re.search(r'^(?:noncomputable\s+)?(?:def|structure|abbrev) (SamplesEfficiently|DrawSamplable|CoreComputable)\b',b):checks['local_contract'].append((f,i,a))
  if re.search(r'^(?:noncomputable\s+)?(?:def|structure|abbrev) .*RealizesOn\b',b):checks['local_realizesOn'].append((f,i,a))
  if re.search(r'\b(sorry|admit)\b',b):admissions.append((f,i,a.strip()))
  if re.search(r'\b(admit|native_decide)\b',b):checks['forbidden_admission'].append((f,i,a))
  if re.search(r'\baxiom\b',b):checks['new_axiom'].append((f,i,a))
  if re.search(r'\b(UniformSampler|CoinSampler)\b.*(where|:=)',b):checks['sampler_instance'].append((f,i,a))
  if re.search(r'∃\s+\w+\s*:\s*NUPPT\s*,.*\.Computes',b):checks['bare_nonuniform_efficiency'].append((f,i,a))
  if re.search(r'\b(invFun|Classical\.choose|exists_pow_eq|pow_val_bijective)\b',b):checks['rdlog'].append((f,i,a))
  if re.search(r'^namespace\s+',b) and not re.search(r'^namespace (TCSlib\.Cryptography\.(Pairing|AdvancedEncryption\.FunctionalEncryption)|Bilinear(Group|Gen)|[A-Za-z0-9_.]+)$',b):checks['namespace'].append((f,i,a))
(out/'boundary.json').write_text(json.dumps(checks,indent=2)+'\n')
(out/'admissions.tsv').write_text('file\tline\ttext\n'+'\n'.join('\t'.join(map(str,x)) for x in admissions)+'\n')
(out/'files.tsv').write_text('file\tlines\twidth\tsha256\n'+'\n'.join('\t'.join(map(str,x)) for x in lines)+'\n')
mods=Path('evidence/logs/order.txt').read_text().splitlines();base_rows=[]
for m in mods:
 f=m+'.lean';old=subprocess.run(['git','show',base+':'+f],capture_output=True,text=True)
 if old.returncode:continue
 a=len(re.findall(r'\b(sorry|admit)\b',lexer.blank(old.stdout)));b=len(re.findall(r'\b(sorry|admit)\b',lexer.blank(Path(f).read_text())))
 base_rows.append((f,a,b,a==b))
(out/'base-admissions.tsv').write_text('file\tbase\thead\tunchanged\n'+'\n'.join('\t'.join(map(str,x)) for x in base_rows)+'\n')
commits=subprocess.check_output(['git','rev-list',base+'..HEAD'],text=True).splitlines();pdf=[]
for c in commits:
 for f in subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',c],text=True).splitlines():
  if f.lower().endswith('.pdf'):pdf.append((c,f))
for f in Path('evidence').rglob('*'):
 if f.is_file() and f.suffix.lower()=='.pdf':pdf.append(('evidence',str(f)))
(out/'no-pdf.json').write_text(json.dumps({'commits_checked':len(commits),'pdf_paths':pdf},indent=2)+'\n')
summary={'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'owned_files':len(files),'owned_lines':sum(x[1] for x in lines),'admissions':len(admissions),'base_admissions_unchanged':all(x[3] for x in base_rows),'checks':{k:len(v) for k,v in checks.items()},'pdf_hits':len(pdf)}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
