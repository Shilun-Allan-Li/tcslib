import sys, json, re
# usage: mkresolve.py <module> <rwargs json> <out>: a copy of the module followed by `#resolve` of every
# identifier (inside `namespace Turing`), printing its kind, reducibility, projection flag and module.
src, js, out = sys.argv[1:4]
ids = sorted(json.load(open(js))['ids'])
ids = [i for i in ids if re.match(r"^[A-Za-z_][\w.']*$", i) and i not in ('by', 'show')
       and not re.search(r'\.\d', i)]   # `h.1`-style projections of locals are not identifiers
tail = r'''
namespace Turing
open Lean Meta Elab Command in
elab "#resolve " ids:ident* : command => do
  for id in ids do
    try
      let n ← liftCoreM <| realizeGlobalConstNoOverload id
      let env ← getEnv
      let some ci := env.find? n | logInfo m!"RES {id.getId} -> {n} MISSING"; continue
      let k := match ci with
        | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      let r ← getReducibilityStatus n
      let rs := match r with | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
      let proj := (env.getProjectionFnInfo? n).isSome
      let mod := match env.getModuleIdxFor? n with
        | some i => toString (env.header.moduleNames[i]!)
        | none => "THIS-FILE"
      logInfo m!"RES {id.getId} -> {n} {k} {rs} proj={proj} {mod}"
    catch _ =>
      logInfo m!"RES {id.getId} UNRESOLVED (local)"
'''
cmd = '#resolve ' + ' '.join(ids) + '\nend Turing\n'
open(out, 'w', encoding='utf-8').write(open(src, encoding='utf-8').read().rstrip('\n') + '\n' + tail + cmd)
print('identifiers', len(ids))
