from pathlib import Path
import json,hashlib
P=Path('/private/tmp/mig-post234-final-head-accounting');c=json.loads((P/'context.json').read_text());imports=''.join('import '+m+'\n'for m in c['primary_owners']+c['context_owners'])+'import Lean\n'
requests=['_private.TCSlib.Complexity.TuringMachine.Build.Catalog.0.Turing.FinTM.f2_extract_run.match_1','_private.TCSlib.Complexity.TuringMachine.Build.Catalog.0.Turing.FinTM.f2_loop_find_run.match_1','_private.TCSlib.Complexity.TuringMachine.Build.Catalog.0.Turing.FinTM.f2_strip_linear.match_1']
probe=imports+'''/-! Export exactly three ordinary generated matcher definitions as structured metadata.
No theorem or opaque proof value is read/rendered. This permits a fresh kernel comparison of
five public type expressions containing these old generated matcher references. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let requests : List String := '''+json.dumps(requests)+'''
  for requestedName in requests do
    let found := env.constants.toList.filter fun (n, _) => n.toString == requestedName
    unless found.length == 1 do throwError "ordinary matcher count {requestedName}: {found.length}"
    let (n, ci) := found.head!
    let .defnInfo di := ci | throwError "refuse non-definition value {n}"
    unless di.safety == .safe do throwError "refuse unsafe/partial definition {n}"
    let some i := env.getModuleIdxFor? n | throwError "no owner {n}"
    let ax ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"ORDINARY_MATCHER|{(Json.mkObj [("name", toJson n.toString),
      ("nameExpr", toJson (reprStr n)), ("owner", toJson env.header.moduleNames[i.toNat]!.toString),
      ("levelParamsExpr", toJson (reprStr di.levelParams)), ("typeExpr", toJson (reprStr di.type)),
      ("valueExpr", toJson (reprStr di.value)), ("hintsExpr", toJson (reprStr di.hints)),
      ("safety", toJson (reprStr di.safety)), ("axioms", toJson ((ax.qsort Name.lt).toList.map Name.toString))]).compress}"
  logInfo "MATCHER_COMPLETE|3|only_ordinary_safe_definition_values"
'''
(P/'TypeTransport-BaseMatchers.lean.txt').write_text(probe);project=Path(c['project']);(project/'TypeTransport-BaseMatchers.lean').write_text(probe);(P/'type-transport-base-job.json').write_text(json.dumps([{'name':'Base-type-matchers','side':'Base','project_file':'TypeTransport-BaseMatchers.lean','evidence_file':'TypeTransport-BaseMatchers.lean.txt'}],indent=2)+'\n');print('prepared',len(probe.encode()),hashlib.sha256(probe.encode()).hexdigest())
