r"""frozen_check_bb1m.py <base-file> <head-file> [--bullet-file <path>]

Frozen-header check of the owned AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean (fill
bb1-machine). Run as `python3 -I frozen_check_bb1m.py <base> <head>`. <base> is the #331 version
(9e7a9648). Reverts exactly the permitted edits in the head file and requires the result to equal
the base file byte for byte:
  (1) added import lines, each `import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.
      BonehBoyenMachine.<Name>` with <Name> one of the fill's helper modules Draws, Handler,
      Oracles, Reduction, Words; the base's imports unchanged and in order; and the whole import
      block equal to the issue base's (7c0a55e0), with ORACLES_IMPORT inserted directly after
      ORACLES_AFTER_IMPORT (the `.Handler` import) when it is present;
  (2) one `## Contents` section of the module docstring, right after the base's
      `## Main definitions\n\nNone.\n` and ending before the next `## ` heading; it must equal
      ISSUE_CONTENTS (the issue base's section) when the Oracles import is absent, and
      ISSUE_CONTENTS with ORACLES_BULLET inserted right after the `BonehBoyenMachine.Reduction`
      bullet when it is present;
  (3) in T4 (`exists_bb1_distinguisher`): the `**Proof sketch.**` paragraph (to the docstring's end)
      and the body after the header's last line
      `      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ) ≤ σ κ := by`
      (to `end TCSlib...`) are replaced by the base's; the head's body must be indented (no
      top-level line, so no declaration can be added there).
Everything else (T4's header and statement prose, the rest of the module docstring, the other
imports) must be byte-identical. Prints PASS or FAIL with the first differing line (exit 0/1).

THE LEAD MAY ADJUST: ORACLES_BULLET (below; or pass --bullet-file <path> holding the bullet text,
ending in a newline), ORACLES_IMPORT and ORACLES_AFTER_IMPORT.

Original: checkpoint/tools/frozen_check_bb1m.py (fill-bb1-machine checkpoint).
ADAPTED (tools-agent, fill bb1-machine):
  - A1 `Oracles` added to the permitted helper modules of (1).
  - A2 new: the head's import block is pinned to the issue base's, with the Oracles import allowed
    only directly after the `.Handler` import (so directly before `.Reduction`).
  - A3 (2) no longer removes any `## Contents` section: the section is required and pinned to the
    issue base's, with exactly the one ORACLES_BULLET added after the Reduction bullet iff the
    Oracles import is present; any other Contents text FAILs.
  - A4 lines rewrapped to at most 100 characters; code split into functions; the base and head are
    read as bytes and decoded as UTF-8 (no newline translation); `--bullet-file` option.
  - (3) (T4 sketch and body) is unchanged in logic.

written by tools-agent (sub-agent), fill bb1-machine (adapted from the checkpoint's tool)
"""
import re
import sys

HP = 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.'
HELPERS = ('Draws', 'Handler', 'Oracles', 'Reduction', 'Words')
ORACLES_IMPORT = HP + 'Oracles\n'
ORACLES_AFTER_IMPORT = HP + 'Handler\n'
ISSUE_IMPORTS = [
    'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen\n',
    HP + 'Draws\n',
    HP + 'Handler\n',
    HP + 'Reduction\n',
    HP + 'Words\n',
    'import TCSlib.Cryptography.Pairing.Assumptions\n',
    'import TCSlib.Cryptography.Pairing.Operations\n',
]
# the issue base's (7c0a55e0) `## Contents` section, from the blank line after `None.` up to (not
# including) the blank line before `## Main results`
ISSUE_CONTENTS = (
    '\n## Contents\n'
    '\n'
    'The machine is built in helper modules:\n'
    '\n'
    '* `BonehBoyenMachine.Draws`: the exponents drawn from coin blocks, their distance from'
    ' uniform,\n'
    '  and the simulator with exponents read from a tape.\n'
    '* `BonehBoyenMachine.Words`: the polynomial-time string functions of the handler.\n'
    '* `BonehBoyenMachine.Handler`: the handler and its run.\n'
    '* `BonehBoyenMachine.Reduction`: the acceptance of the T1 machine and the comparison of the'
    ' drawn\n'
    '  with the ideal exponents.\n')
REDUCTION_BULLET = (
    '* `BonehBoyenMachine.Reduction`: the acceptance of the T1 machine and the comparison of the'
    ' drawn\n'
    '  with the ideal exponents.\n')
ORACLES_BULLET = (
    '* `BonehBoyenMachine.Oracles`: the simulator\'s oracles as `drawStep` with fresh exponents,'
    ' call by\n'
    '  call, and the comparison of the simulation with the machine on one Decision BDH tuple.\n')
HL = ('      advantage (bb1SimGame G ℓ A (q.eval κ) b real κ) (G.dbdhGame (D b) real κ)'
      ' ≤ σ κ := by\n')
END = '\nend TCSlib.Cryptography.AdvancedEncryption.IdentityBased\n'
ANCHOR = '## Main definitions\n\nNone.\n'


def fail(msg):
    print('FAIL:', msg)
    sys.exit(1)


def first_diff(x, y):
    xl, yl = x.split('\n'), y.split('\n')
    n = min(len(xl), len(yl))
    k = next((i for i in range(n) if xl[i] != yl[i]), n)
    return (k + 1, xl[k] if k < len(xl) else None, yl[k] if k < len(yl) else None)


def read(p):
    with open(p, 'rb') as fh:
        return fh.read().decode('utf-8')


def cut(s, tag):
    if s.count(HL) != 1:
        fail(f'{tag}: T4 header end line not found exactly once')
    if not s.endswith(END):
        fail(f'{tag}: file end changed')
    a = s.index(HL) + len(HL)
    body = s[a:len(s) - len(END)]
    t4 = s.index('theorem exists_bb1_distinguisher')
    ds = s.rfind('/--', 0, t4)
    ps = s.find('**Proof sketch.**', ds, t4)
    if ps < 0:
        fail(f'{tag}: no proof sketch in T4 docstring')
    pe = s.index('-/\n', ps)
    return s[:ps], s[pe:a], body, s[ps:pe]


def main(argv):
    args = argv[1:]
    bullet = ORACLES_BULLET
    if '--bullet-file' in args:
        k = args.index('--bullet-file')
        bullet = read(args[k + 1])
        del args[k:k + 2]
    if len(args) != 2:
        print(__doc__)
        return 2
    base, head = read(args[0]), read(args[1])
    # (1) imports
    bi = re.findall(r'^import \S+\n', base, re.M)
    hi = re.findall(r'^import \S+\n', head, re.M)
    added = [x for x in hi if x not in bi]
    for x in added:
        if not (x.startswith(HP) and x[len(HP):].strip() in HELPERS):
            fail(f'added import not a helper: {x!r}')
    if [x for x in hi if x in bi] != bi:
        fail('base imports changed or reordered')
    oracles = ORACLES_IMPORT in hi
    exp_imports = list(ISSUE_IMPORTS)
    if oracles:
        exp_imports.insert(exp_imports.index(ORACLES_AFTER_IMPORT) + 1, ORACLES_IMPORT)
    if hi != exp_imports:
        k, x, y = first_diff(''.join(exp_imports), ''.join(hi))
        fail(f'import block differs from the issue base{" + Oracles" if oracles else ""} at '
             f'import {k}: expected {x!r} head {y!r}')
    h = head
    for x in added:
        h = h.replace(x, '', 1)
    # (2) Contents
    if h.count(ANCHOR) != 1:
        fail('Main definitions anchor missing or repeated')
    i = h.index(ANCHOR) + len(ANCHOR)
    if not h[i:].startswith('\n## Contents\n'):
        fail('## Contents section missing right after `## Main definitions`')
    j = h.index('\n## ', i + 1)
    sec = h[i:j]
    exp = ISSUE_CONTENTS
    if oracles:
        if exp.count(REDUCTION_BULLET) != 1:
            fail('internal: Reduction bullet not found once in ISSUE_CONTENTS')
        exp = exp.replace(REDUCTION_BULLET, REDUCTION_BULLET + bullet)
    if sec != exp:
        k, x, y = first_diff(exp, sec)
        fail(f'## Contents differs from the issue base{" + Oracles bullet" if oracles else ""} '
             f'at section line {k}: expected {x!r} head {y!r}')
    h = h[:i] + h[j:]
    # (3) T4 sketch and body
    b0, b1, bb, bs = cut(base, 'base')
    h0, h1, hb, hs = cut(h, 'head')
    if hb.strip() == '':
        fail('T4 body empty')
    for ln in hb.split('\n'):
        if ln and not ln.startswith(' '):
            fail(f'top-level line in T4 body: {ln!r}')
    if 'sorry' not in bb:
        fail('base T4 body not sorry')
    for x, y, nm in ((b0, h0, 'before T4 sketch'), (b1, h1, 'T4 header')):
        if x != y:
            k, xl, yl = first_diff(x, y)
            fail(f'{nm} differs at line {k}: base {xl!r} head {yl!r}')
    print(f'PASS: {len(added)} helper import(s) added'
          f'{" (incl. Oracles, after .Handler)" if oracles else ""}; Contents section = issue '
          f'base{" + Oracles bullet" if oracles else ""}; T4 header and statement prose '
          f'byte-identical; T4 sketch {"unchanged" if hs == bs else "replaced"};'
          f' T4 body {"unchanged (sorry)" if hb == bb else "replaced"}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
