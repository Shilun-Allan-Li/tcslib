from pathlib import Path
import json,sys,hashlib
P=Path('/private/tmp/mig-post234-compiled-accounting');mode=sys.argv[1];assert mode in ['initial-not-final','final'];ctx=json.loads((P/'preparation.json').read_text());selected=json.loads((P/(mode+'-selected-source-roots.json')).read_text());assert not selected['historical144_roots_missing_current_source']
imports=''.join('import '+m+'\n'for m in ctx['primary_owners']+ctx['context_owners'])+'import Lean\n'
requested='[\n'+',\n'.join('    ('+json.dumps(r['owner'])+', '+json.dumps(r['name'])+', '+str(r['private']).lower()+')'for r in selected['roots'])+'\n  ]'
s=imports+'''/-! Read-only source-root/descendant/direct-citation probe. No theorem proof value is
rendered; value expressions are inspected only for their direct referenced constant names. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let requested : List (String × String × Bool) := '''+requested+'''
  let kind := fun (ci : ConstantInfo) => match ci with
    | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
    | .axiomInfo _ => "axiom" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"
  for (owner, sourceName, priv) in requested do
    let matches := env.constants.toList.filter fun (n, _) =>
      isPrivateName n == priv && (n.toString == sourceName || n.toString.endsWith ("." ++ sourceName)) &&
      match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString == owner
      | none => false
    unless matches.length == 1 do
      throwError "source root {owner}/{sourceName} private={priv} has {matches.length} matches"
    let (root, rootCI) := matches.head!
    unless kind rootCI == "theorem" do throwError "source proof root is not a theorem {root}"
    logInfo m!"ROOTMAP|{(Json.mkObj [("source_name", toJson sourceName),
      ("compiled_name", toJson root.toString), ("owner", toJson owner),
      ("private", toJson priv), ("kind", toJson (kind rootCI))]).compress}"
    let descendants := env.constants.toList.filter fun (n, _) => root.isPrefixOf n
    for (n, ci) in descendants.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
      let some i := env.getModuleIdxFor? n | throwError "source descendant lacks owner {n}"
      let home := env.header.moduleNames[i.toNat]!
      let ax ← liftCoreM <| Lean.collectAxioms n
      logInfo m!"ROOTDESC|{(Json.mkObj [("root", toJson root.toString),
        ("name", toJson n.toString), ("owner", toJson home.toString),
        ("kind", toJson (kind ci)), ("private", toJson (isPrivateName n)),
        ("internal", toJson n.isInternalDetail),
        ("axioms", toJson ((ax.qsort Name.lt).toList.map Name.toString))]).compress}"
      for (part, expr) in [("type", ci.type)] ++ (ci.value?.map (fun e => [("value", e)])).getD [] do
        for c in expr.getUsedConstants.qsort Name.lt do
          let some j := env.getModuleIdxFor? c | continue
          let mod := env.header.moduleNames[j.toNat]!
          unless (`TCSlib).isPrefixOf mod do continue
          let some cinfo := env.find? c | throwError "referenced constant absent {c}"
          logInfo m!"CITED|{(Json.mkObj [("root", toJson root.toString),
            ("descendant", toJson n.toString), ("part", toJson part),
            ("name", toJson c.toString), ("owner", toJson mod.toString),
            ("kind", toJson (kind cinfo)), ("private", toJson (isPrivateName c))]).compress}"
  logInfo m!"ROOTCOMPLETE|{requested.length}"
'''
assert 'reprStr'not in s and 'VALUE_REPR'not in s
name=('SourceRoots-'+mode+'.lean.txt');(P/name).write_text(s)
(P/('root-probe-'+mode+'-preparation.json')).write_text(json.dumps({'source':selected['source'],'stage':mode,'root_count':selected['selected_root_count'],'target_count':17,'repair_count':14,'historical_rehome_preserved':selected['historical_root_rehomes'],'probe':name,'probe_sha256':hashlib.sha256(s.encode()).hexdigest(),'no_theorem_proof_value_rendering':True,'direct_type_value_constant_references_only':True,'not_executed':True},indent=2)+'\n')
print(name,len(s.encode()),hashlib.sha256(s.encode()).hexdigest(),selected['selected_root_count'])
