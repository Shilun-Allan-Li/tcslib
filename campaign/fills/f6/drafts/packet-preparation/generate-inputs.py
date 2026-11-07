"""Reproduce F6 source-only order lists; never compile or fetch a cache.
python3 -I generate-inputs.py --repo CHECKOUT --rev COMMIT --parser IMPORT_PARSER --out NEW_DIR
The parser's imports_of function is used; its historical Diagonal main is never called.
"""
from pathlib import Path
import argparse,hashlib,json,runpy,subprocess
ap=argparse.ArgumentParser()
for k in ["repo","rev","parser","out"]:ap.add_argument("--"+k,required=True)
a=ap.parse_args();w=Path(a.repo).resolve();o=Path(a.out).resolve();o.mkdir()
def git(*args):return subprocess.check_output(["git","-C",str(w),*args],text=True).strip()
rev=git("rev-parse",a.rev);subprocess.run(["git","-C",str(w),"cat-file","-e",rev+"^{commit}"],check=True)
assert not git("diff",rev,"--","*.lean"),"Source must equal the pinned commit"
parse=runpy.run_path(a.parser)["imports_of"]
paths=[p for p in git("ls-tree","-r","--name-only",rev).splitlines() if p.endswith(".lean") and (p.startswith("TCSlib/") or p=="TCSlib.lean")]
mods={p[:-5].replace("/","."):parse(str(w/p)) for p in paths}
target="TCSlib.Complexity.SpaceComplexity.Hierarchy"
reverse={}
for m,imps in mods.items():
 for i in imps:reverse.setdefault(i,set()).add(m)
def topo(roots):
 out=[];state={}
 def visit(m):
  if state.get(m)==2:return
  assert state.get(m)!=1,("cycle",m);state[m]=1
  for i in sorted(mods[m]):
   if i.startswith("TCSlib"):assert i in mods,("missing",i);visit(i)
  state[m]=2;out.append(m)
 for m in sorted(roots):visit(m)
 return out
boot=topo([target]);down=set();todo=[target]
while todo:
 m=todo.pop()
 if m in down:continue
 down.add(m);todo.extend(reverse.get(m,()))
down.discard("TCSlib");final=topo(down);downorder=[m for m in final if m in down]
assert "TCSlib" not in final and "TCSlib" not in boot
for n,order in [("bootstrap-order.txt",boot),("downstream-order.txt",downorder),("final-order.txt",final)]:
 (o/n).write_text("".join(m.replace(".","/")+"\n" for m in order))
mathlib=sorted({i for m in final for i in mods[m] if i.startswith("Mathlib.")})
(o/"mathlib-roots.txt").write_text("\n".join(mathlib)+"\n")
external=sorted({i for m in final for i in mods[m] if not i.startswith("TCSlib")})
(o/"external-imports.txt").write_text("\n".join(external)+"\n")
inputs=[]
for m in final:
 p=m.replace(".","/")+".lean";b=(w/p).read_bytes();blob=git("rev-parse",rev+":"+p);assert git("hash-object",p)==blob
 inputs.append({"path":p,"git_blob":blob,"sha256":hashlib.sha256(b).hexdigest(),"imports":mods[m]})
(o/"source-inputs.json").write_text(json.dumps(inputs,indent=2)+"\n")
print(json.dumps({"source":rev,"bootstrap":len(boot),"downstream":len(downorder),"final":len(final),"Mathlib_roots":len(mathlib)}))
