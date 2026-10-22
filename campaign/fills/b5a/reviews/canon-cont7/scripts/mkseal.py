#!/usr/bin/env python3
"""Build the reviewer's seal and its control files from the head module.

usage: mkseal.py <head module> <seal names file> <out dir> <home line> <stub body end line>
  home line:      the head line before which the sealed section opens (first new line, 4953)
  stub body end:  the last line of the stub's proof (8074); the section closes after it
Writes into <out dir>:
  C7SealBody.lean       the module with the owned region inside `section C7Seal`, every name
                        `attribute [local irreducible]` at the section's top: must elaborate clean
  C7SealCtl.lean        the same with one `#seal_control` per name at the section's top and at
                        its end, plus the worker's `counterValue` rfl control: every control must
                        fail (2N + 1 errors) and the body must stay clean
  C7UnsealedCtl.lean    the controls without the attribute: every control must close (0 errors)
The `#seal_control` command (defined in a preamble after the imports' namespace-free top) checks
`@f =?= value(f)` at default transparency, the check `rfl` makes.
"""
import os, sys
src, namesf, outd, home, stub_end = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
names = [l.strip() for l in open(namesf) if l.strip()]
L = open(src, encoding='utf-8').read().rstrip('\n').split('\n')
assert L[home - 2].strip() == '', L[home - 2]
assert L[home - 1].startswith('/-- A successful record skip'), L[home - 1]
assert L[stub_end - 1].strip() == '(by omega) b' and L[stub_end].strip() == '', (L[stub_end - 1], L[stub_end])
last_import = max(i for i, l in enumerate(L) if l.startswith('import '))
preamble = r'''
open Lean Elab Command Meta in
/-- Reviewer's `rfl` control: does `@f` close against its own delta-unfolded value at default
transparency (the check `rfl` makes)? Logs an error when it does not. -/
elab "#seal_control " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM do
    let ci ← getConstInfo n
    let some v := ci.value? | throwError "CONTROL {n}: no value"
    let us := ci.levelParams.map mkLevelParam
    let ok ← withTransparency .default <| isDefEq (mkConst n us) v
    if ok then logInfo m!"CONTROL {n}: rfl closes"
    else logError m!"CONTROL {n}: rfl fails"
'''.split('\n')
# structurally recursive definitions do not delta-unfold against their compiled value; their
# controls are concrete source-level `rfl` examples instead (each closes unsealed)
CONCRETE = {
    'Turing.incFixed': 'example : Turing.incFixed [false] = some [true] := rfl',
    'Turing.codeReadUnary': 'example : Turing.codeReadUnary [false] = some (0, []) := rfl',
    'Turing.codeSkipRepeat': 'example : Turing.codeSkipRepeat (fun _ => none) 0 [] = some [] := rfl',
    'Turing.pairDecode': 'example : Turing.pairDecode [false, true] = some ([], []) := rfl',
}
def controls(tag):
    out = [f'-- reviewer controls ({tag})']
    out += [CONCRETE.get(n, f'#seal_control {n}') for n in names]
    out += ['example : Turing.counterValue [true] = 1 := rfl']
    return out
attr = ['attribute [local irreducible]'] + ['  ' + n for n in names]
def build(seal, ctl):
    body = L[:last_import + 1] + preamble + L[last_import + 1:home - 1]
    body += ['section C7Seal'] + (attr if seal else []) + [''] + (controls('top') if ctl else []) + ['']
    body += L[home - 1:stub_end]
    body += [''] + (controls('end') if ctl else []) + ['end C7Seal'] + L[stub_end:]
    return '\n'.join(body) + '\n'
os.makedirs(outd, exist_ok=True)
for fn, seal, ctl in (('C7SealBody.lean', True, False), ('C7SealCtl.lean', True, True),
                      ('C7UnsealedCtl.lean', False, True)):
    open(os.path.join(outd, fn), 'w', encoding='utf-8').write(build(seal, ctl))
print(f'{len(names)} names; files written to {outd}')
