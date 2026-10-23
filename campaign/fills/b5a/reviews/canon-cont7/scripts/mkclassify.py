#!/usr/bin/env python3
"""usage: mkclassify.py <module file> <rwargs json> <out file>
Appends `#classify` over every non-term argument head of the inventory, inside
`namespace Turing.MachineFormat` (the owned region's namespace), resolving each name as the
region would (private names of the module included)."""
import json, sys
src, js, out = sys.argv[1:4]
import re
heads = [k for k in json.load(open(js))['idents'] if not k.startswith('<term>') and k != 'show' and not re.search(r'\.\d', k)]
t = open(src, encoding='utf-8').read().rstrip('\n')
tail = r'''

open Lean Elab Command in
elab "#classify " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let rs ← liftCoreM <| (do
      let r ← resolveGlobalName id.getId
      pure (r.filter (·.2.isEmpty) |>.map (·.1))) <|> pure []
    match rs with
    | [] => logInfo m!"CLASS {id.getId}: unresolved (a local)"
    | n :: _ =>
      let kind := match env.find? n with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEFINITION"
        | some (.ctorInfo _) => "ctor"
        | some (.inductInfo _) => "inductive"
        | some (.opaqueInfo _) => "opaque"
        | some (.axiomInfo _) => "axiom"
        | some _ => "other"
        | none => "?"
      let m := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i]?.map toString).getD "?"
        | none => "this module"
      logInfo m!"CLASS {id.getId}: {kind} {n} [{m}]"

namespace Turing
namespace MachineFormat
'''
cmd = '#classify ' + ' '.join(heads)
open(out, 'w', encoding='utf-8').write(t + tail + cmd + '\nend MachineFormat\nend Turing\n')
print(len(heads), 'heads')
