from pathlib import Path
import json,re,difflib,hashlib,ast
O=Path(__file__).parent;plans={
'TCSlib/Complexity/CookLevin/Hardness.lean':[
('''**Proof sketch.** Minimize the all-returned occurrence before the common
proved deadline. Absorption implies that its first occurrence already has
the exact endpoint and restored heads.''','''**Proof sketch.** Apply the public fixed-stop first-entry theorem to the
all-returned state and the proved deadline. Whole-configuration stationarity
preserves the exact endpoint and restored heads at that first entry.'''),
('''**Proof sketch.** Choose the first completed-control occurrence below the exact copying bound. Since completion is absorbing on the whole configuration, its first occurrence already has the final record and restored source head. Initial and completed controls are distinct.''','''**Proof sketch.** Apply the public fixed-stop first-entry theorem to the
completed control and the exact copying bound. Its first entry preserves the
final record and restored source head. Distinct initial and completed controls
make the selected time positive.'''),
('''**Proof sketch.** Minimize the completed-control occurrence below the
proved copying bound. The completed controller is absorbing, so its
first occurrence has the exact word and all the restored counter heads.''','''**Proof sketch.** Apply the public fixed-stop first-entry theorem to the
completed control and the proved copying bound. Stationarity preserves the
exact word and restored counter heads. The nonzero field count excludes an
initial completed control and makes the selected time positive.'''),
('''**Proof sketch.** Cut the exact completed run at its first completed-state
occurrence. Whole-configuration absorption preserves both the verdict and
all read-only words. The disjoint initial phase excludes zero duration.''','''**Proof sketch.** Apply the public fixed-stop first-entry theorem with both
completed verdicts in its stop predicate. It preserves the exact arithmetic
verdict and all read-only words. The disjoint initial phase excludes zero
duration.'''),
('''**Proof sketch.** Minimize the return-control occurrence. Absorption makes
its whole configuration identical to the known endpoint, not just its state.''','''**Proof sketch.** Specialize the public fixed-stop first-entry theorem to the
return control. It preserves the complete known endpoint; the initial-control
exclusion makes the selected time positive.'''),
('''**Proof sketch.** Consume the banked comparator and native loader, then cut
at the first completed verdict. Absorption of either completed source verdict
rules out an earlier different verdict. The replay wrapper follows every
preceding source transition and emits exactly one bit on its halting step.''','''**Proof sketch.** Consume the banked comparator and native loader, then cut
at the first completed verdict. The public fixed-stop first-entry theorem,
with both verdicts in its predicate, supplies the wider guard at the same
complete endpoint. The replay wrapper follows every preceding source
transition and emits exactly one bit on its halting step.''')],
'TCSlib/Complexity/TuringMachine/Build/InputCall.lean':[
('''**Proof sketch.** Invoke the public rewind with exit `left`, then move left once. Since
`done` is stationary, reaching it before the public rewind's `left` endpoint is impossible.''','''**Proof sketch.** Invoke the public rewind with exit `left`, then move left once.
Apply the public fixed-stop first-entry theorem to the stationary `done` control,
retaining the exact parked endpoint and the prefix work-head bounds.''')],
'TCSlib/Complexity/TuringMachine/Build/InputLength.lean':[
('''The counter head stays in `[pos - 1, pos + |bits |x||]`. -/''','''The counter head stays in `[pos - 1, pos + |bits |x||]`. The public fixed-stop
first-entry theorem cuts the completed return without changing its exact framed
endpoint or these head bounds. -/''')],
'TCSlib/Complexity/ClassNP/EXP.lean':[
('''the same full endpoint and no earlier anchor visit. Absorption identifies
the first endpoint with the supplied bounded endpoint. -/''','''the same full endpoint and no earlier anchor visit. Absorption identifies
the first endpoint with the supplied bounded endpoint.
**Proof sketch.** Apply the public fixed-stop first-entry theorem to the stopped
machine, then use the off-anchor prefix agreement to transfer the cut and full
endpoint to the active machine. -/''')]
}
# Extract only our own newly authored lexical comment reader, without running its collector body.
mod=ast.parse((O/'enumerate_candidates.py').read_text());node=next(n for n in mod.body if isinstance(n,ast.FunctionDef) and n.name=='strip');ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),'own-comment-reader','exec'),ns);strip=ns['strip'];patch=[];rows=[]
for path,repls in plans.items():
 old=(O/'draft-source'/(path+'.txt')).read_text();new=old
 for before,after in repls:assert new.count(before)==1,(path,before[:80]);new=new.replace(before,after)
 assert re.findall(r'\S+',strip(old))==re.findall(r'\S+',strip(new)),path
 out=O/'sketch-source'/(path+'.txt');out.parent.mkdir(parents=True,exist_ok=True);out.write_text(new)
 patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path));rows.append({'path':path,'draft_before_sha256':hashlib.sha256(old.encode()).hexdigest(),'sketch_after_sha256':hashlib.sha256(new.encode()).hexdigest(),'comment_stripped_code_tokens_exact':True,'code_sha256':hashlib.sha256(' '.join(re.findall(r'\S+',strip(new))).encode()).hexdigest(),'native_execution':'No separate execution of comment-only variant; exact code equality to checked body draft. Root may apply after body patch.'})
(O/'sketch-sync-after-body.patch').write_text(''.join(patch));(O/'SKETCH-SYNC.json').write_text(json.dumps(rows,indent=2)+'\n');print('sketch sync files',len(rows),'code unchanged')
# Audit new/removed tactic lines; whole unchanged legacy operational proofs are not globally approved.
added=[]
for path in sorted({m['path'] for m in json.loads((O/'DRAFT-SOURCE-MAP.json').read_text())}):
 old=(O/'source'/(path+'.txt')).read_text();new=(O/'draft-source'/(path+'.txt')).read_text();diff=list(difflib.unified_diff(old.splitlines(),new.splitlines(),n=0))
 for ln in diff:
  if ln.startswith('+') and not ln.startswith('+++') and re.search(r'\b(simp|simpa|simp_all|simp_rw|rw|dsimp|unfold|delta|norm_num)\b',ln):added.append({'path':path,'added_tactic_line':ln[1:]})
allowed={'MultiTapeTM.runFrom_zero':'public theorem/Deterministic','MultiTapeTM.runFrom_succ_eq_step\'':'public theorem/Deterministic','MultiTapeTM.step_of_some':'public theorem/Deterministic','FinTM.controlAction_apply':'public theorem/Simulation','moveInputPos_zero':'public theorem/Configuration','step_of_inputMoveAction':'public theorem/Catalog','FinTM.moveInputPos_neg_val':'public theorem/Simulation','clCopyCfg':'same-home private definition/Hardness','clRowCfg':'same-home private definition/Hardness','clPreparedCfg':'same-home private definition/Hardness','clPlacedCfg_eq':'same-home private theorem/Hardness','enumCont_agree_run':'same-home private theorem/EXP','result':'local let','hq':'local hypothesis','hz':'local equality','hret':'local hypothesis','hend':'local hypothesis','he':'local equality','hrun':'local hypothesis','same':'local equality','finish':'local hypothesis'}
foreign_forbidden=['[Option.map]','[Action.mapState]','[Cfg.mapState]','[MultiTapeTM.runFrom]','[MultiTapeTM.step]','[seamCompTM]']
assert not any(any(s in d['added_tactic_line'] for s in foreign_forbidden) for d in added)
audit={'scope':'Newly added tactic lines of exact11-body patch; explicit argument review, not whole legacy-proof Rule10 clearance','added_tactic_lines':added,'published_or_same_home_or_local_heads':allowed,'new_forbidden_explicit_Core_Mathlib_or_other_file_TCS_definition_arguments':0,'hand_review':'All new bracketed heads resolve to local equalities/lets, same-home private definitions/theorems, or the named published equations. The wider comparator new result-state proof uses same-home clPlacedCfg_eq. InputCall stationarity uses public step/controlAction equations rather than identifying controlAction/inputMoveAction by foreign delta.','unchanged_legacy_boundary':['Hardness.clA5Compare_compute retains its prior seamCompTM initialization and other operational-reader lines literally outside the replacement guard.','InputLength.exists_inputLengthTM retains prior counting/rewind proof and explicit Cfg.inputSymbol read literally outside the inline cut.','Two-guard seals test complete declarations at runFrom/step only; they are not claimed as complete foreign-definition closure seals.']};(O/'EXPLICIT-ARGUMENT-REVIEW.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n');print('new tactic lines audited',len(added))
