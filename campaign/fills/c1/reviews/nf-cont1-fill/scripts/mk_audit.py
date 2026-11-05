# mk_audit.py <module> <names.txt> <out.lean>: module + my audit tail (axioms, census, walk, seal candidates)
import sys
mod, names_f, out = sys.argv[1:4]
src = open(mod, encoding='utf-8').read()
names = [l.strip() for l in open(names_f) if l.strip()] + ['exists_codeNDTM_accepts_linear']
tail = ['', '-- ===== review audit tail (reviewer-written) =====', 'open Turing Turing.FinNDTM', '']
for n in names:
    tail.append(f'#print axioms Turing.FinNDTM.{n}')
tail.append('')
tail.append(r'''
open Lean in
partial def rvConstsAux (e : Expr) : StateM (Std.HashSet Expr × Std.HashSet Name) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, a)
  match e with
  | .const n _ => modify fun (v, a) => (v, a.insert n)
  | .app f x => rvConstsAux f; rvConstsAux x
  | .lam _ t b _ => rvConstsAux t; rvConstsAux b
  | .forallE _ t b _ => rvConstsAux t; rvConstsAux b
  | .letE _ t v b _ => rvConstsAux t; rvConstsAux v; rvConstsAux b
  | .mdata _ b => rvConstsAux b
  | .proj _ _ b => rvConstsAux b
  | _ => pure ()

open Lean in
def rvConsts (ci : ConstantInfo) : Array Name :=
  let act : StateM (Std.HashSet Expr × Std.HashSet Name) Unit := do
    rvConstsAux ci.type
    if let some v := ci.value? then rvConstsAux v
  ((act.run ({}, {})).2.2).toArray

open Lean Elab Command Meta in
elab "#rv_audit" : command => do
  let env ← getEnv
  let newRoots : Array Name := #[NAMES]
  let locals := env.constants.map₂.foldl (init := (#[] : Array (Name × ConstantInfo))) fun acc n ci => acc.push (n, ci)
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let modOf : Name → Name := fun n => match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => `LOCAL
  let isNew : Name → Bool := fun n =>
    let u := (privateToUserName? n).getD n
    newRoots.any (fun r => (`Turing.FinNDTM ++ r).isPrefixOf u) || !isPrivateName n
  let mut pub : Array String := #[]
  let mut nPriv : Nat := 0
  let mut outside : Array String := #[]
  let mut sorryUsers : Array String := #[]
  let mut nNew : Nat := 0
  let mut reached : Std.HashSet Name := {}
  for (n, ci) in locals do
    if isPrivateName n then nPriv := nPriv + 1 else pub := pub.push n.toString
    let axs ← collectAxioms n
    if axs.any (fun a => !std.contains a) then outside := outside.push s!"{n}: {axs}"
    if (rvConsts ci).contains ``sorryAx then sorryUsers := sorryUsers.push n.toString
    if isNew n then
      nNew := nNew + 1
      for c in rvConsts ci do
        if (modOf c) != `LOCAL then reached := reached.insert c
  logInfo m!"CENSUS locals={locals.size} private={nPriv} public={pub.size} new(incl aux)={nNew}\nPUBLIC {pub.qsort (· < ·)}\nOUTSIDE_STD {outside}\nDIRECT_SORRY {sorryUsers}"
  -- the walk: direct external constants of the new declarations (and their auxiliaries)
  let mut tc : Array String := #[]
  let mut oth : Nat := 0
  let mut tcDefs : Array String := #[]
  for c in reached.toArray.qsort (fun a b => a.toString < b.toString) do
    let m := modOf c
    if (`TCSlib).isPrefixOf m then
      let ci := env.find? c |>.get!
      let kind := match ci with
        | .defnInfo _ => "def" | .thmInfo _ => "thm" | .ctorInfo _ => "ctor" | .inductInfo _ => "induct"
        | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      let red ← getReducibilityStatus c
      let inst ← liftCoreM (isInstance c)
      let proj := env.isProjectionFn c
      let mat := isMatcherCore env c
      let aux := isAuxRecursor env c || isNoConfusion env c
      let line := s!"{c} | {m} | {kind} | {repr red} | inst={inst} proj={proj} matcher={mat} auxrec={aux}"
      tc := tc.push line
      if kind == "def" then tcDefs := tcDefs.push line
    else oth := oth + 1
  logInfo m!"WALK external={reached.size} tcslib={tc.size} other={oth}\n{String.intercalate "\n" tc.toList}"
  logInfo m!"WALK_TCSLIB_DEFS {tcDefs.size}\n{String.intercalate "\n" tcDefs.toList}"
  -- maximal seal candidates: every imported TCSlib definition, semireducible, not a projection,
  -- matcher or auxiliary recursor
  let st ← liftTermElabM getSimpTheorems
  let mut cand : Array String := #[]
  let mut simpDefs : Array String := #[]
  for (c, ci) in env.constants.map₁.toList do
    if (`TCSlib).isPrefixOf (modOf c) then
      if let .defnInfo _ := ci then
        if st.isDeclToUnfold c then simpDefs := simpDefs.push c.toString
        let red ← getReducibilityStatus c
        if red matches .semireducible && !env.isProjectionFn c && !isMatcherCore env c && !isAuxRecursor env c &&
            !isNoConfusion env c && !(privateToUserName? c).isSome then
          let inst ← liftCoreM (isInstance c)
          cand := cand.push s!"{c} inst={inst}"
  logInfo m!"SEAL_CANDIDATES {cand.size}\n{String.intercalate "\n" (cand.qsort (· < ·)).toList}\nSIMP_DEFS {simpDefs.qsort (· < ·)}"

#rv_audit
'''.replace('NAMES', ', '.join('`' + n for n in names)))
open(out, 'w', encoding='utf-8').write(src + '\n'.join(tail) + '\n')
print('wrote', out)
