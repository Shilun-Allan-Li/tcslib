from pathlib import Path
import subprocess,re,hashlib,json
root=Path('/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange')
out=Path('/private/tmp/io-phfe-drafts/audit')
paths=subprocess.run(['git','diff','--name-only','5ed465f62e4ae0f93ded1a1ba49e807591b589eb'],cwd=root,capture_output=True,text=True,check=True).stdout.splitlines()
files={p:root/p for p in paths if p.endswith('.lean')}
for p in Path('/private/tmp/io-phfe-drafts/PHFE').glob('*.lean'):
 rel='TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/'+p.name
 if rel not in files: files[rel]=p
# Current worktree takes precedence over draft headers already copied by the root.
def strip(s):
 a=list(s);i=0;depth=0;line=False;quoted=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':a[i:i+2]='  ';depth+=1;i+=2;continue
   if s[i:i+2]=='-/':a[i:i+2]='  ';depth-=1;i+=2;continue
   if s[i]!='\n':a[i]=' '
   i+=1;continue
  if line:
   if s[i]=='\n':line=False
   else:a[i]=' '
   i+=1;continue
  if s[i:i+2]=='/-':a[i:i+2]='  ';depth=1;i+=2;continue
  if s[i:i+2]=='--':a[i:i+2]='  ';line=True;i+=2;continue
  i+=1
 return ''.join(a)
patterns={
 'prohibited-import':r'^import\s+(?:TCSlib\.Programs\b|TCSlib\.Complexity\.RAMSimulation\b|TCSlib\.Cryptography\.Games\.Closeness\b|TCSlib\.Cryptography\.CoinSampling\.(?!Efficiency\b|Contract\b)\S+)',
 'forbidden-contract-declaration':r'^(?:(?:noncomputable|protected|private)\s+)*(?:def|abbrev|structure|class|axiom)\s+(?:\S*\.)?(?:RealizesOn|SamplesEfficiently|DrawSamplable|CoreComputable)\b',
 'exponent-extraction-token':r'\b(?:invFun|Classical\.choose|exists_pow_eq|pow_val_bijective)\b',
 'prohibited-proof-token':r'\b(?:axiom|native_decide|admit)\b',
 'global-simp':r'@\[simp\]|attribute\s+\[simp\]',
 'machine-construction-token':r'\b(?:PolyHandler|exists_handlerMachine|Programs\.)\b',
 'bare-machine-efficiency':r'∃\s+\w+\s*:\s*NUPPT\s*,\s*\w+\.Computes\b',
}
hits=[];manifest=[];decl=[];admissions=[];imports=[]
for rel,p in sorted(files.items()):
 s=p.read_text();code=strip(s);ls=s.splitlines()
 manifest.append([rel,str(p),str(len(ls)),str(max(map(len,ls),default=0)),hashlib.sha256(s.encode()).hexdigest()])
 for name,pat in patterns.items():
  for m in re.finditer(pat,code,re.M):
   ln=code.count('\n',0,m.start())+1;hits.append([name,rel,str(ln),ls[ln-1].strip()])
 for ln,l in enumerate(ls,1):
  if len(l)>100:hits.append(['width>100',rel,str(ln),str(len(l))])
 for m in re.finditer(r'\bsorry\b',code):
  ln=code.count('\n',0,m.start())+1;admissions.append([rel,str(ln)])
 for m in re.finditer(r'^import\s+(\S+)',code,re.M):imports.append([rel,m[1]])
 for m in re.finditer(r'^(?:(?:noncomputable|protected|private)\s+)*(def|abbrev|structure|theorem|lemma|instance)\s+([\w.\x27]+)',code,re.M):
  ln=code.count('\n',0,m.start())+1;decl.append([rel,str(ln),m[1],m[2]])
for name,header,data in [('snapshot.tsv','repository_path\tphysical_path\tlines\tmax_width\tsha256',manifest),('boundary-hits.tsv','category\tfile\tline\ttext',hits),('declarations.tsv','file\tline\tkind\tname_as_declared',decl),('admissions.tsv','file\tline',admissions),('imports.tsv','file\timport',imports)]:
 (out/name).write_text(header+'\n'+'\n'.join('\t'.join(r) for r in data)+'\n')
summary={'files':len(files),'lines':sum(int(r[2]) for r in manifest),'source_declarations':len(decl),'sorry_occurrences':len(admissions),'hits_by_category':{k:sum(h[0]==k for h in hits) for k in [*patterns,'width>100']},'pdf_paths_in_diff':[p for p in paths if p.lower().endswith('.pdf')],'not_run':['Lean','lake','build','Rule10 seals','exact?/apply?','axiom census','proof audit']}
(out/'static-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2));print('HITS',hits[:30])
