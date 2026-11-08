from pathlib import Path
import json,hashlib,subprocess,datetime
O=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup/review/round3-image-repoint')
C=json.loads((O/'context.json').read_text());W=Path(C['worktree']);p=W/'TCSlib/Complexity/ClassNP/Tautology.lean'
for name in ['Hypothetical-native-v1','Hypothetical-sealed-v1']:
    r=json.loads((O/(name+'-run.json')).read_text());assert (r['exit'],r['errors'])==(0,0)
assert subprocess.check_output(['git','-C',str(W),'rev-parse','HEAD']).decode().strip()==C['source_head_at_preparation']
assert subprocess.check_output(['git','-C',str(W),'status','--porcelain'])==b''
assert p.read_bytes()==(O/'Tautology-before.lean.txt').read_bytes()
b=(O/'Tautology-proposed.lean.txt').read_bytes()
assert hashlib.sha256(b).hexdigest()==C['proposed_sha256']
p.write_bytes(b)
assert p.read_bytes()==b
for rel,pin in C['source_pins'].items():
    if rel.endswith('/Tautology.lean'):continue
    assert hashlib.sha256((W/rel).read_bytes()).hexdigest()==pin['sha256'],rel
meta=(O/'metadata-append.lean.txt').read_bytes()
(O/'Tautology-actual-native-v1.lean.txt').write_bytes(b+meta)
chunk=(O/'target-after.lean.txt').read_bytes();assert b.count(chunk)==1
names=(O/'guard-definitions.txt').read_text().splitlines()
guard=('section G106ImageSeal\nattribute [local irreducible] '+' '.join(names)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n\n').encode()
tail=b'end G106ImageSeal\n\n'
sealed=b.replace(chunk,guard+chunk+tail,1)
assert sealed.replace(guard+chunk+tail,chunk,1)==b
(O/'Tautology-actual-sealed-v1.lean.txt').write_bytes(sealed+meta)
(O/'instrumentation.json').write_text(json.dumps({'target':'taut_comp_on_image','guard_before_complete_docstring_header_body':True,'guard':guard.decode(),'suffix':tail.decode(),'default_simp_removed':['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],'guard_removal_recovers_exact_full_actual_source':True,'native_append_removal_recovers_exact_full_actual_source':True,'actual_source_sha256':hashlib.sha256(b).hexdigest(),'direct_explicit_proof_arguments':'M U f g T₁ T₂ hM hU; public theorem only; no rw/simp/unfold/change arguments','no_private_alias_or_unsafe_reducibility':True},indent=2)+'\n')
status=subprocess.check_output(['git','-C',str(W),'status','--porcelain']).decode()
assert status==' M TCSlib/Complexity/ClassNP/Tautology.lean\n',repr(status)
receipt={'applied_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'head_unchanged':C['source_head_at_preparation'],'file':'TCSlib/Complexity/ClassNP/Tautology.lean','before_sha256':C['source_pins']['TCSlib/Complexity/ClassNP/Tautology.lean']['sha256'],'after_sha256':hashlib.sha256(b).hexdigest(),'after_bytes':len(b),'only_dirty_path':'TCSlib/Complexity/ClassNP/Tautology.lean','SAT_and_Hardness_exact_original_bytes':True,'actual_edit_after_hypothetical_native_and_seal_pass':True,'root_released_after_MSG6_PASS':True}
(O/'apply-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(O/'apply_source.py').write_bytes(Path(__file__).read_bytes())
(O/'run_probe.py').write_bytes((Path(C['scratch'])/'run_probe.py').read_bytes())
print(json.dumps(receipt,indent=2))
