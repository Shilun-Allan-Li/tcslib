from pathlib import Path
import json,shutil
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());P=O/'live/catalog-project';P.mkdir(parents=True,exist_ok=True);(P/'.lake').mkdir(exist_ok=True);(P/'.lake/packages').symlink_to(Path(pin['source_worktree'])/'.lake/packages',target_is_directory=True);shutil.copyfile(O/'context/lean-toolchain',P/'lean-toolchain')
union={r['name'] for r in json.loads((O/'ORDINARY-UNION.json').read_text())};extra=['Turing.Cfg.init','Complexity.LogProg.ctr','Complexity.LogProg.rlen','Complexity.LogProg.cellOff','Turing.FinTM.VirtualTag','Complexity.LogProg.mkCfg','Complexity.LogProg.regPos','Complexity.LogProg.retPos','Complexity.LogProg.TPos.Valid','Complexity.LogProg.Consistent','Complexity.LogProg.trackPos','Complexity.LogProg.inPos','Complexity.LogProg.ccfg','Complexity.LogProg.markI','Complexity.LogProg.PB','Function.Embedding.coe_refl','List.map_id','List.length_map','one_mul','Finset.mem_image','Finset.mem_range','Finset.coe_range','Set.mem_Iio','Finset.card_range','Finset.card_univ','Fintype.card_prod','Fintype.card_option','Fintype.card_fin','Fintype.card_pi','Finset.prod_const','Fintype.card_bool','Prod.mk.injEq','Fin.mk.injEq','Function.comp_apply','Fin.append_left','Fin.append_right','Fin.val_zero','Nat.not_lt_zero','lt_self_iff_false','Fin.is_lt','Nat.nsmul_eq_mul','Finset.mem_filter','Finset.sum_const','List.idxOf_lt_length_of_mem'];names=sorted(union|set(extra));imports=['import Lean']+['import '+r['path'][:-5].replace('/','.') for r in pin['source_files']]
code='\n'.join(imports)+'''\nset_option maxHeartbeats 0
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let wanted : List Name := ['''+', '.join('`'+n for n in names)+''']
  let homeOf := fun (n : Name) => match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  let kind := fun (ci : ConstantInfo) => match ci with
    | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
  let entries := env.constants.toList
  for n in wanted do
    let some ci := env.find? n | logInfo m!"MISSING|{n}"; continue
    let hints := match ci with
      | .defnInfo di => match di.hints with
        | .abbrev => "abbrev" | .opaque => "opaque" | .regular _ => "regular"
      | _ => "not_definition"
    logInfo m!"CATALOG|{(Json.mkObj [("name",toJson n.toString),("owner",toJson (homeOf n).toString),("kind",toJson (kind ci)),("hints",toJson hints),("projection",toJson (env.isProjectionFn n)),("type",toJson (reprStr ci.type))]).compress}"
    if (homeOf n).toString.startsWith "TCSlib." then
      let prefix := n.toString.toLower
      for (r, info) in entries do
        if info matches .thmInfo _ then
          if r.toString.toLower.startsWith prefix && !isPrivateName r then
            let ty ← liftTermElabM <| Meta.ppExpr info.type
            logInfo m!"READER|{(Json.mkObj [("definition",toJson n.toString),("name",toJson r.toString),("owner",toJson (homeOf r).toString),("typeExpr",toJson (reprStr info.type)),("typePretty",toJson ty.pretty)]).compress}"
  logInfo m!"CATALOG_COMPLETE|{wanted.length}"
'''
(P/'Catalog.lean').write_text(code);(O/'Catalog.lean.txt').write_text(code);(O/'CATALOG-REQUEST.json').write_text(json.dumps({'ordinary_definitions_are_unchanged_between_MAC8_and_current_FH':'ALL17-CODE-PRESERVATION.json in prior frozen export; this probe reads only definition/type metadata from MAC8, not current FH proof values.','names':names,'no_proof_values_read_or_rendered':True},indent=2)+'\n');print('Catalog names',len(names))
