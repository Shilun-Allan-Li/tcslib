import sys
# usage: mkdirect.py <module file> <out file> <full names...>: append a command that lists, for each
# root, the constants it uses directly (through its own auxiliary constants `root.*` only), split
# into other-module TCSlib constants, other-module non-TCSlib constants, and own-module constants.
src, out, names = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(src, encoding='utf-8').read().split('\n')
last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
lines.insert(last_import + 1, 'import Lean.Util.FoldConsts')
tail = r'''
open Lean Elab Command in
elab "#direct_uses " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[n]
  let mut tcs : NameSet := {}
  let mut other : NameSet := {}
  let mut own : NameSet := {}
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet.toList do
        match env.getModuleIdxFor? d with
        | some i =>
          if ((env.header.moduleNames[i]?.map (·.getRoot == `TCSlib)).getD false) then
            tcs := tcs.insert d
          else other := other.insert d
        | none =>
          if n.isPrefixOf d && d != n then
            unless visited.contains d do stack := stack.push d
          else if d != n then own := own.insert d
  let srt (s : NameSet) := ((s.toList.map toString).toArray.qsort (· < ·))
  logInfo m!"DIRECT {n}\n TCSLIB {srt tcs}\n OTHER {srt other}\n OWN {srt own}"
'''
cmds = [f'#direct_uses {n}' for n in names]
open(out, 'w', encoding='utf-8').write('\n'.join(lines).rstrip('\n') + '\n' + tail + '\n' + '\n'.join(cmds) + '\n')
print('commands', len(cmds))
