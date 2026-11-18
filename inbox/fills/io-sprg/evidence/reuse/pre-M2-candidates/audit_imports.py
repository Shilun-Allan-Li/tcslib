from pathlib import Path
import re,json,subprocess
root=Path.cwd();out=Path(__file__).resolve().parent;cache={};missing=set()
def strip_comments(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif string:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
def locate(mod):
 bases=[root]
 if mod.startswith('Mathlib.') or mod=='Mathlib':bases.insert(0,root/'.lake/packages/mathlib')
 if mod.startswith('Batteries.') or mod=='Batteries':bases.insert(0,root/'.lake/packages/batteries')
 for base in bases:
  p=base/(mod.replace('.','/')+'.lean')
  if p.is_file():return p
 return None
def deps(mod):
 if mod not in cache:
  p=locate(mod)
  if p:cache[mod]=[word for line in re.findall(r'^(?:public )?import\s+([^\n]+)',strip_comments(p.read_text()),re.M) for word in line.split()]
  else:cache[mod]=[];missing.add(mod)
 return cache[mod]
def clos(mod):
 seen=set();todo=[mod]
 while todo:
  m=todo.pop()
  if m not in seen:seen.add(m);todo.extend(deps(m))
 return seen
owners=['Degree','Buckets','SparseFactor','PolyTerms','Stretch','Claim42','Claim42.Load','Params','Encoding','Polys','Correctness']
want=['Mathlib.Algebra.MonoidAlgebra.Degree','Mathlib.Data.Finsupp.Weight','Mathlib.Data.Sum.Basic','Mathlib.Data.Option.Basic','Mathlib.Data.List.FinRange','Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Algebra.BigOperators.Group.Finset.Basic','Mathlib.Algebra.MvPolynomial.Variables','Mathlib.Algebra.Order.Ring.Basic','Mathlib.Data.Nat.Cast.Order.Field','Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics','Mathlib.Analysis.SpecialFunctions.Pow.Real','Mathlib.Analysis.SpecificLimits.Basic','Mathlib.Analysis.Asymptotics.SpecificAsymptotics','Mathlib.Algebra.Order.Floor.Semiring','Mathlib.Algebra.Order.Floor.Semifield','Mathlib.Algebra.Order.Floor.Div','Mathlib.Data.Nat.Choose.Bounds','Mathlib.Analysis.Complex.Exponential','Mathlib.Analysis.SpecialFunctions.Exp','Mathlib.Analysis.SpecialFunctions.Log.Base','Mathlib.Analysis.SpecialFunctions.Stirling','TCSlib.Complexity.Randomized.PolyExpr','TCSlib.Cryptography.Foundations.Subexponential']
cs={o:clos('TCSlib.Cryptography.Obfuscation.StructuredSeed.'+o) for o in owners}
result={o:{'size':len(c),'selected_present':[w for w in want if w in c],'selected_absent':[w for w in want if w not in c]} for o,c in cs.items()}
meta={'candidate':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'owners':result,'missing_source_modules':sorted(missing),'method':'Nested Lean comments and strings stripped before following actual imports; unlocated Init/Lean/provider roots recorded but not built; no Lean executed.'}
(out/'import-closure-audit.json').write_text(json.dumps(meta,indent=2)+'\n')
(out/'import-closures.json').write_text(json.dumps({o:sorted(c) for o,c in cs.items()},indent=2)+'\n')
print(json.dumps({'candidate':meta['candidate'],'Stretch_FloorSemifield_present':'Mathlib.Algebra.Order.Floor.Semifield' in cs['Stretch'],'Degree_selected_found':all(m in cs['Degree'] for m in ['Mathlib.Algebra.MonoidAlgebra.Degree','Mathlib.Data.Finsupp.Weight','Mathlib.Data.Sum.Basic']),'Load_factorial_sources_present':all(m in cs['Claim42.Load'] for m in ['Mathlib.Data.Nat.Choose.Bounds','Mathlib.Analysis.Complex.Exponential']),'owner_count':len(owners)}))
