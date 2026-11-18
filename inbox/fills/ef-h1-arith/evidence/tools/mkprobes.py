# mkprobes.py <out-dir> <module>...: StmtDump.lean (every public constant of the modules, full name,
# kind and type) and Axioms.lean (#print axioms of each), both outside the library.
import sys, os
out, mods = sys.argv[1], sys.argv[2:]
os.makedirs(out, exist_ok=True)
imp = ''.join(f'import {m}\n' for m in mods)
mlist = ', '.join('`' + m for m in mods)
open(os.path.join(out, 'StmtDump.lean'), 'w').write(imp + f'''
open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  for m in #[{mlist}] do
    let some idx := env.getModuleIdx? m | throwError "no module"
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if isPrivateName c then continue
      let some ci := env.find? c | continue
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | _ => "other"
      let ty ← liftTermElabM (ppExpr ci.type)
      logInfo m!"STMT {{m}} {{kind}} {{c}} : {{ty}}"
''')
