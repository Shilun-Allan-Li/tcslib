#!/usr/bin/env python3
"""For each changed or new file of the nm-cca2 fill, write a census module with exactly the file's
imports. It lists every seal candidate of the file's full TCSlib import closure: every TCSlib
definition (`defnInfo`) that is not reducible, not an instance, not a structure projection, not an
auxiliary recursor or `noConfusion`, and not private or internal. Since the census imports only
the file's imports, every TCSlib definition it sees is foreign to the file. (The helper modules are
foreign to each other and to the owned file.)"""
import re, sys
F = '/workspace/fill'
D = 'TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/'
FILES = {
  'Readers': D + 'Indistinguishability/Readers.lean',
  'Forward': D + 'Indistinguishability/Forward.lean',
  'Decrypt': D + 'Indistinguishability/Decrypt.lean',
  'Encrypt': D + 'Indistinguishability/Encrypt.lean',
  'Owned': D + 'Indistinguishability.lean',
}
BODY = '''
open Lean Elab Command Meta

/-! Seal census of the nm-cca2 fill for `%s`: the module's own imports, and every seal candidate
of its full TCSlib import closure (semireducible (neither reducible nor already irreducible), non-instance, non-projection, non-private
TCSlib definitions; all are foreign to the file). One `CAND` line each. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  let mut skipped : Nat := 0
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.toString.startsWith "TCSlib" do continue
    unless ci matches .defnInfo _ do continue
    if c.isInternal || isPrivateName c then skipped := skipped + 1; continue
    if isInstanceCore env c || env.isProjectionFn c || isAuxRecursor env c ||
        isNoConfusion env c then skipped := skipped + 1; continue
    if getReducibilityStatusCore env c != .semireducible then skipped := skipped + 1; continue
    out := out.push s!"CAND {c.toString (escape := true)} | {mod}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size} candidates; {skipped} TCSlib definitions skipped"
'''
def imports(path):
    return [l.rstrip('\n') for l in open(F + '/' + path) if l.startswith('import ')]
src_over = dict(a.split('=', 1) for a in sys.argv[1:])  # Name=alternative source path (base)
for name, path in list(FILES.items()) + [(k, v) for k, v in src_over.items()]:
    p = src_over.get(name, path) if name in FILES else path
    imps = imports(p)
    open(F + '/scratch/seal/Scan%s.lean' % name, 'w').write('\n'.join(imps) + '\n' + BODY % p)
    print(name, p, len(imps))
