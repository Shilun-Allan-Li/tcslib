from pathlib import Path
import json,hashlib,subprocess,datetime
O=Path(__file__).parent;C=json.loads((O/'CONTEXT.json').read_text());R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');H=lambda b:hashlib.sha256(b).hexdigest();G=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a])
F=json.loads((O/'SOURCE-FREEZE.json').read_text())
for r in F['bindings']:
 b=(O/'source/BASE'/(r['path']+'.txt')).read_bytes();assert b==G('show',C['source']+':'+r['path']);assert H(b)==r['BASE_SHA256'];assert H((O/'source/CANDIDATE'/(r['path']+'.txt')).read_bytes())==r['CANDIDATE_SHA256']
(O/'helpers').mkdir(exist_ok=True)
for name,path in C['approved_helper_paths'].items():
 b=Path(path).read_bytes();assert H(b)==C['approved_helper_SHA256'][name];(O/'helpers'/name).write_bytes(b)
primary=Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Lean/Expr.lean');lines=primary.read_text().splitlines();(O/'LEAN-EXPR-ALPHA-EQUALITY-REFERENCE.txt').write_text('\n'.join(lines[779:795])+'\n');(O/'LEAN-EXPR-REFERENCE.json').write_text(json.dumps({'path':str(primary),'SHA256':H(primary.read_bytes()),'excerpt_1based_lines':[780,795],'purpose':'Primary local Lean4.25 documentation distinguishes alpha Expr.eqv from binder-name-sensitive Expr.equal. The proof-data comparison itself is fully recorded and not relabelled as a Lean-executed eqv check.'},indent=2)+'\n')
(O/'README.md').write_text('Start PROPOSAL.md. This is a concrete private feasibility proposal requiring Seyoon’s ruling; no checkout adoption. SOURCE-FREEZE.json and PROPOSED-EXACT-MOVE.patch pin the exact move. SELECTED-CHECKS.json, full SELECTED-*.json and raw runs retain complete selected type/proof/AX/privacy/attribute data, including automatic universe/hygiene changes. RULE10-FOOTPRINT.json and the Configuration-only explicit generic argument check define the Rule10 boundary. Input/output895 object maps establish original snapshot integrity and complete private context. The 1003 tracked Lean Git bindings and 930 extracted TCSlib source checks are distinguished. Native/metadata runs use verified approved leanelab helpers sequentially. The large private runtime/object clone is outside this export packet and is only pointed to by CONTEXT.json.\n')
files=[];exclude={'MANIFEST.json','SHA256SUMS','FROZEN.json'}
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in exclude:files.append({'path':str(p.relative_to(O)),'bytes':p.stat().st_size,'SHA256':H(p.read_bytes())})
(O/'MANIFEST.json').write_text(json.dumps({'frozen_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files),'self_hash_policy':'MANIFEST.json, SHA256SUMS and FROZEN.json excluded to avoid circular hashes; SHA256SUMS covers MANIFEST, FROZEN pins both.'},indent=2)+'\n')
sums=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ['SHA256SUMS','FROZEN.json']:sums.append(H(p.read_bytes())+'  '+str(p.relative_to(O)))
(O/'SHA256SUMS').write_text('\n'.join(sums)+'\n');frozen={'directory':str(O),'source':C['source'],'frozen_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'MANIFEST_SHA256':H((O/'MANIFEST.json').read_bytes()),'SHA256SUMS_SHA256':H((O/'SHA256SUMS').read_bytes()),'PROPOSAL_SHA256':H((O/'PROPOSAL.md').read_bytes()),'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files),'needs_Seyoon_home_change_ruling':True,'no_source_checkout_Git_R_X_adoption_or_mutation':True,'original895_snapshot_objects_unchanged':True};(O/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n');print(json.dumps(frozen,indent=2))
