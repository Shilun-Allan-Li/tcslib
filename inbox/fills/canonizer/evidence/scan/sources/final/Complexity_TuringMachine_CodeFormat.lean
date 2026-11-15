import TCSlib.Complexity.TuringMachine.CodeFormat
open Lean Elab Command

namespace Turing
open Turing.CodeFormat

def idsToCheck : List String := ["F.canonical_eq","F.numStates_assemble","F.parseFull_sound","F.readTable_append","F.readTable_erase","F.serialize_assemble","Function.comp_def","List.all_replicate","List.append_assoc","List.finRange_succ","List.length_append","List.length_cons","List.length_nil","List.length_replicate","Option.bind","Option.bind_assoc","Option.bind_eq_some_iff","Option.getD_some","Option.map_bind","Option.map_eq_bind","Option.map_none","Option.map_some","Option.some.injEq","Prod.mk.injEq","actionBits","actionBitsK","actionBits_eq_actionBitsK","actionBits₂","bind","canonical","codeBitsNat_bits","codeEraseActionK","codeEraseActionK_one","codeEraseFin","codeEraseOutput","codeEraseSign","codeEraseSymbols","codeEraseVec","codeEraseWrite","codeErase_bind","codeReadActionK","codeReadActionK_append","codeReadFin_append","codeReadFin_sound","codeReadOutput_append","codeReadOutput_sound","codeReadSign_append","codeReadSign_sound","codeReadState_append","codeReadState_sound","codeReadVec_sound","codeReadWork","codeReadWrite_append","codeReadWrite_sound","codeSkipAction","codeSkipActionK","codeSkipAction_eq_codeSkipActionK","codeSkipRepeat","codeSkipWork","codeTable2Bits","decode","eq_pairEncode_of_pairDecode","h","h1","hg","ho","hp","hs","htable","hv","hw","id_eq","if_neg","ite_self","length_pairEncode","ne_eq","not_true_eq_false","optStateBits","pairDecode_pairEncode","pairEncode","parseFull","parseFull_serialize_pad","pure","reduceIte","scan","scan_full","unaryFin"]
def scannedModule : Name := `TCSlib.Complexity.TuringMachine.CodeFormat

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    if cands.isEmpty then IO.println s!"{s}\t-\tlocal/unresolved\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\t{c}\t{tag}\t{m}"

end Turing
