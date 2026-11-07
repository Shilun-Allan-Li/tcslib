"""Wrap the explicitly inventoried 42 delivery sections, preserving all other source bytes."""
from pathlib import Path
import ast,os,re,json,hashlib,sys
out=Path(__file__).resolve().parent;source=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad/TCSlib/Complexity/TuringMachine/Build/Primitives.lean';text=source.read_text()
inventory=out.parents[1]/'review/checkpoint07-2026-11-07/extracted/fill-mig1-mega-cp07/evidence/seal/Seal_Primitives.gen'
# This is a names-only receipt, never a script or executable source.
line=inventory.read_text().strip();names=line.split(': ',1)[1].split(', ');assert len(names)==len(set(names))==42
irr=next(n.value.value for n in ast.walk(ast.parse((out/'make_probe.py').read_text())) if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='irr' for x in n.targets))
decl=re.compile(r'^(?:private )?(?:lemma|theorem|def|abbrev|inductive|instance|structure)\b',re.M)
all_decls=[m.start() for m in decl.finditer(text)];docs=[m.start() for m in re.finditer(r'^/--',text,re.M)];stops=[m.start() for m in re.finditer(r'^(?:end |namespace |attribute |section )',text,re.M)]
regions=[]
for i,name in enumerate(names):
 short=name.removeprefix('Turing.FinTM.');matches=list(re.finditer(r'^(?:private )?(?:lemma|theorem|def|inductive|instance)\s+'+re.escape(short)+r'(?=\s|[(:{])',text,re.M));assert len(matches)==1,(name,len(matches));ds=matches[0].start()
 prior_decl=max([x for x in all_decls if x<ds],default=-1);prior_doc=max([x for x in docs if x<ds],default=-1)
 start=prior_doc if prior_doc>prior_decl else ds
 end=min([x for x in all_decls+docs+stops if x>ds],default=len(text))
 regions.append({'name':name,'start':start,'end':end,'header':'section PrimitivesRepair'+str(i)+'\nattribute [local irreducible] '+irr+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n','footer':'\nend PrimitivesRepair'+str(i)+'\n','source_chunk_sha256':hashlib.sha256(text[start:end].encode()).hexdigest()})
sorted_r=sorted(regions,key=lambda x:x['start']);assert all(a['end']<=b['start'] for a,b in zip(sorted_r,sorted_r[1:]))
result=text
for r in reversed(sorted_r):result=result[:r['start']]+r['header']+result[r['start']:r['end']]+r['footer']+result[r['end']:]
restored=result
for r in regions:restored=restored.replace(r['header'],'',1).replace(r['footer'],'',1)
assert restored==text
label=sys.argv[1];target=out/(label+'.lean.txt');assert not target.exists();target.write_text(result)
(out/(label+'-manifest.json')).write_text(json.dumps({'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'sealed_input_sha256':hashlib.sha256(result.encode()).hexdigest(),'definitions':irr.split(),'sections':len(regions),'restores_exact_source':True,'regions':regions},indent=2)+'\n')
print(label,'sections',len(regions),'definitions',len(irr.split()),'source restores exactly')
