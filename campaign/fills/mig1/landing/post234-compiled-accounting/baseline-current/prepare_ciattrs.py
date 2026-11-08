from pathlib import Path
import json,hashlib
P=Path('/private/tmp/mig-post234-compiled-accounting');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');ctx=json.loads((P/'preparation.json').read_text())
s=(R/'campaign/gates/106-sg1-dedup/review/round3-final-compiled/Metadata-ciattrs-v1.lean.txt').read_text()
# The complete trusted source was read before this adaptation. Preserve its structural CI
# and reflected-attribute behavior, explicitly omitting all rendered simp proof expressions.
start=s.index('set_option maxHeartbeats')
s=''.join('import '+m+'\n'for m in ctx['primary_owners']+ctx['context_owners'])+'import Lean\n\n'+s[start:]
old='''  let owners : List Name := [`TCSlib.Complexity.ClassNP.SAT, `TCSlib.Complexity.ClassNP.Tautology,
    `TCSlib.Complexity.CookLevin.Hardness, `TCSlib.Complexity.SpaceComplexity.Machines.Frag,
    `TCSlib.Complexity.TuringMachine.Build.Catalog, `TCSlib.Complexity.TuringMachine.Build.Contract.Basic,
    `TCSlib.Complexity.TuringMachine.Build.CounterLoop, `TCSlib.Complexity.TuringMachine.Build.Primitives,
    `TCSlib.Complexity.TuringMachine.Robustness.SingleTape]'''
assert s.count(old)==2
s=s.replace(old,'  let owners : List Name := ['+', '.join('`'+m for m in ctx['primary_owners']+ctx['context_owners'])+']')
old='("levelParams", metadataNames s.levelParams.toList), ("proof_repr", toJson (reprStr s.proof))'
assert s.count(old)==1
s=s.replace(old,'("levelParams", metadataNames s.levelParams.toList),\n            ("proof_head_constant", toJson (s.proof.getAppFn.constName?.map Name.toString)),\n            ("proof_used_constants", metadataNames s.proof.getUsedConstants.toList)')
assert 'reprStr s.proof' not in s and 'reprStr ci.value'not in s and 'VALUE_REPR'not in s
(P/'Metadata-ciattrs.lean.txt').write_text(s)
project=Path(ctx['project']);(project/'Base-ciattrs.lean').write_text(s)
(P/'ciattrs-preparation.json').write_text(json.dumps({'adapted_from':'campaign/gates/106-sg1-dedup/review/round3-final-compiled/Metadata-ciattrs-v1.lean.txt','trusted_source_sha256':hashlib.sha256((R/'campaign/gates/106-sg1-dedup/review/round3-final-compiled/Metadata-ciattrs-v1.lean.txt').read_bytes()).hexdigest(),'adaptations':['exact12MIGprimary+Finitecontextimports/owners','simp proof expression rendering omitted; head/reference constants only'],'probe_sha256':hashlib.sha256(s.encode()).hexdigest(),'no_theorem_proof_value_rendering':True,'includes_structural_CI_and_reflected_attributes':True,'CI_recursor_rule_rhs_not_theorem_value':True,'HEAD_not_run':True},indent=2)+'\n')
print(s)
