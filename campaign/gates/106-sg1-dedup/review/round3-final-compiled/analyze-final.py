"""Classify the complete native delta and every conservative changed source proof root."""
from pathlib import Path
import base64,collections,difflib,gzip,hashlib,json,re
P=Path(__file__).resolve().parent
STANDARD={"propext","Classical.choice","Quot.sound"}
def load(n):return json.loads((P/n).read_text())
def write(n,x):(P/n).write_text(json.dumps(x,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
a=load("map-Base.json");b=load("map-Head.json");d=load("comparison-staged.json")
namespace={}; parser=(P/"tools/declfreeze.py.txt").read_text()
exec(compile(parser.split("a = chunks(open(sys.argv[1]).read())")[0],"<trusted-authored-identity-parser>","exec"),namespace)
sources={label:{owner:namespace["chunks"]((P/"source"/label/(owner.replace(".","/")+".lean.txt")).read_text()) for owner in (P/"original9-owners.txt").read_text().splitlines()} for label in ["base","head"]}
def authored(label,n,row):
 matches=[s for s,pr,t in sources[label][row["owner"]] if (n.endswith("."+s) if pr else n==s)]
 assert len(matches)<=1,(label,n,matches)
 return matches[0] if matches else None
classes={}
for key,label in [("added","head"),("removed","base")]:
 classes[key]=[]
 for n,row in d[key].items():
  src=authored(label,n,row)
  classes[key].append(dict(name=n,owner=row["owner"],kind=row["kind"],private=row["private"],internal=row["internal"],category=("authored private source declaration" if row["private"] else "authored nonprivate source declaration") if src else "compiler-generated auxiliary",source_name=src,axioms=row["axioms"]))
 assert sum(x["source_name"] is not None for x in classes[key])==3
 assert all(x["private"] for x in classes[key])
classes["shared_field_changes"]={field:[dict(name=n,owner=a["census"][n]["owner"],private=a["census"][n]["private"],source_name=authored("head",n,b["census"][n]),before=a["census"][n][field],after=b["census"][n][field]) for n in names] for field,names in d["common_field_changes"].items()}
classes["method"]="Exact compiler identities retained, with full source-qualified suffix matching used only to associate authored private declarations in their actual owner. No private-ID normalization; unmatched additions/removals are compiler auxiliaries, not source API removals."
write("delta-classification.json",classes)
assert not any(d["nonprivate_common_field_changes"].values())
assert not d["simp_rule_changes"] and not d["nonstandard_axiom_regressions"] and not d["added_nonstandard_axioms"]
assert d["nonstandard_name_sets_equal"]
for n in a["nonstandard_axioms"]:
 assert all(a["census"][n][f]==b["census"][n][f] for f in ["owner","kind","private","internal","ci","attributes","axioms"])
 assert a["census"][n]["type_repr"]["sha256"]==b["census"][n]["type_repr"]["sha256"]
source=load("source-authored-inventory.json")
roots=[]
for ownerrow in source["owners"]:
 owner=ownerrow["owner"]
 candidates=[(r["name"],r["private"],"changed surviving source proof chunk") for r in ownerrow["changed_chunks"]]
 candidates += [(r["name"],r["private"],"added private replacement proof") for r in ownerrow["authored_added"]]
 for src,pr,why in candidates:
  matches=[n for n,row in b["census"].items() if row["owner"]==owner and row["private"]==pr and (n.endswith("."+src) if pr else n==src)]
  assert len(matches)==1,(owner,src,matches)
  n=matches[0]; row=b["census"][n]; assert row["kind"]=="theorem"
  desc=sorted(k for k in b["census"] if k.startswith(n+"."))
  roots.append(dict(name=n,source_name=src,owner=owner,private=pr,kind=row["kind"],reason=why,axioms=row["axioms"],descendants=[dict(name=k,kind=b["census"][k]["kind"],private=b["census"][k]["private"],axioms=b["census"][k]["axioms"]) for k in desc]))
assert len(roots)==43 and len({r["name"] for r in roots})==43
selected={r["name"] for r in roots}|{d["name"] for r in roots for d in r["descendants"]}
assert all(set(b["census"][n]["axioms"])<=STANDARD for n in selected)
write("all-current-repaired-roots.json",dict(method="All40 conservative source-chunk changes (including comment changes) plus3 authored private replacements, resolved to exact current compiler identities in owner/private namespace. Every prefix descendant is retained; complete ALLAX already covers the whole owner population.",root_count=len(roots),public_roots=sum(not r["private"] for r in roots),private_roots=sum(r["private"] for r in roots),descendant_count=len(selected)-len(roots),selected_count=len(selected),all_standard=True,roots=roots))
write("inherited-nonstandard-closure.json",dict(method="Full ALLAX name sets and complete row equality; nonstandard inherited closure remains exactly equal, not cleared by this repair.",base=a["nonstandard_axioms"],head=b["nonstandard_axioms"],same=True,constant_count=len(b["nonstandard_axioms"])))
write("owned-simp-rules.json",dict(base=a["simp_rules"],head=b["simp_rules"],exact_effective_rules_equal=a["simp_rules"]==b["simp_rules"],base_total=sum(map(len,a["simp_rules"].values())),head_total=sum(map(len,b["simp_rules"].values()))))
old=json.loads((P.parent/"round3-current-compiled/map-Head.json").read_text()); oldc=old["census"];newc=b["census"];common=set(oldc)&set(newc)
fields=["owner","kind","private","internal","ci","attributes","type_repr","axioms"]
change={f:[n for n in sorted(common) if (oldc[n][f]["sha256"]!=newc[n][f]["sha256"] if f=="type_repr" else oldc[n][f]!=newc[n][f])] for f in fields}
write("historical-D0-to-final79.json",dict(historical_head=old["commit"],current_head=b["commit"],historical_counts=old["counts"],current_counts=b["counts"],added={n:newc[n] for n in sorted(set(newc)-set(oldc))},removed={n:oldc[n] for n in sorted(set(oldc)-set(newc))},shared_field_changes=change,limit="Historical D0 is not the audit head. This secondary comparison explains the need for fresh final HEAD; BASE remains3023/MAC4."))
changed=set(d["common_field_changes"]["type_repr"]);text={}
for label in ["Base","Head"]:
 raw=gzip.decompress(base64.decodebytes((P/(label+"-types-v1.out.gz.b64")).read_bytes())).decode()
 markers=list(re.finditer(r"^(TYPE_REPR|TYPECOMPLETE)\|([^|\n]+)(?:\|)?",raw,re.M)); chunks=[];found=set()
 for i,m in enumerate(markers[:-1]):
  if m[2] in changed:chunks.append(raw[m.start():markers[i+1].start()]);found.add(m[2])
 assert found==changed
 text[label]="".join(chunks);(P/("changed-shared-types-"+label+".txt")).write_text(text[label])
(P/"changed-shared-types.patch").write_text("".join(difflib.unified_diff(text["Base"].splitlines(keepends=True),text["Head"].splitlines(keepends=True),fromfile="BASE exact raw shared types",tofile="final HEAD exact raw shared types")))
summary=dict(base=d["base"],head=d["head"],base_counts=a["counts"],head_counts=b["counts"],added_classes=dict(collections.Counter(r["category"] for r in classes["added"])),removed_classes=dict(collections.Counter(r["category"] for r in classes["removed"])),shared_field_change_counts={k:len(v) for k,v in d["common_field_changes"].items()},public_field_change_counts={k:len(v) for k,v in d["nonprivate_common_field_changes"].items()},all43_current_roots_plus_descendants_standard=True,proof_root_count=len(roots),proof_descendant_count=len(selected)-len(roots),owned_simp_rules=sum(map(len,b["simp_rules"].values())),simp_rules_exact=True,inherited_nonstandard_unchanged=len(b["nonstandard_axioms"]),no_formerly_proved_constant_acquired_nonstandard_axiom=True,generated_nonprivate_additions=0,source_public_additions=0,source_public_removals=0,limits="Complete unfiltered owned census/type/CI/AX/reflected attributes, no ConstantInfo proof/value rendering, no new legacy seal/fill/replay or gate closure. Axiom results are scoped; inherited nine Primitives sorry closures remain.")
write("summary.json",summary);print(json.dumps(summary,indent=2))
