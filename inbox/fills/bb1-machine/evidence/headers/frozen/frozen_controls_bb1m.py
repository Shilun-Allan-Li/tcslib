"""frozen_controls_bb1m.py <base-file> <head-file> <checker> <outdir> [<checker-args>...]

Mutation controls of frozen_check_bb1m.py (fill bb1-machine): frozen_controls.py's harness with
mutations of BonehBoyenMachine.lean. Run as `python3 -I`. Each control applies one
single-occurrence edit to the head file (written to <outdir>/<control>.lean) and must make the
checker FAIL; the unmutated head must PASS. Prints one line per control and
`ALL_CONTROLS_OK True|False` (exit 0/1). Extra <checker-args> (e.g. `--bullet-file <path>`)
are passed to every checker run. A control whose anchor does not occur exactly once in the
head is reported as `ANCHOR-NOT-UNIQUE` and counts as not OK (fix the anchor; never drop the
control).

Original: checkpoint/tools/frozen_controls_bb1m.py (fill-bb1-machine checkpoint).
ADAPTED (tools-agent, fill bb1-machine):
  - C1-C8 kept with their edits. C3's anchor was lengthened from 'negligible `σ` with' to
    'negligible `σ` with `|Pr[bb1SimGame' so that it stays unique if the new sketch reuses the
    phrase (the edit, `with` -> `such that`, is unchanged). C6's anchor (`.Words` import ->
    `.Words2`) and the others still apply once on the mock head.
  - New: C9a deletes the blank line between the statement prose and `**Proof sketch.**`; C9b
    changes the last word of the prose line just above it (`distributions.` ->
    `distribution.`): both spill from the sketch into the statement prose.
  - New: C10a rewords an existing `## Contents` bullet (Handler); C10b adds an unpermitted bullet
    after the Reduction bullet; C10b2 adds a second new bullet after the Oracles bullet; C10c
    drops the Oracles bullet while keeping its import; C10d drops the Oracles import while
    keeping the bullet. (C10b2/C10c/C10d are skipped, and reported SKIP, on a head without the
    Oracles import.)
  - New: C11a moves the Oracles import after `.Reduction`; C11b moves it to the end of the
    import block. (Skipped on a head without the Oracles import.)
  - Extra checker arguments are passed through. The unmutated head's check output is printed in
    full; failures print the checker's last line; the subprocess uses `sys.executable -I`; lines
    at most 100 characters.

written by tools-agent (sub-agent), fill bb1-machine (adapted from the checkpoint's tool)
"""
import os
import subprocess
import sys

HP = 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.'
ORA = HP + 'Oracles\n'
ORA_BULLET_START = '* `BonehBoyenMachine.Oracles`:'
END = '\nend TCSlib.Cryptography.AdvancedEncryption.IdentityBased\n'
RED = ('* `BonehBoyenMachine.Reduction`: the acceptance of the T1 machine and the comparison of the'
       ' drawn\n  with the ideal exponents.\n')


def read(p):
    with open(p, 'rb') as fh:
        return fh.read().decode('utf-8')


def write(p, s):
    with open(p, 'wb') as fh:
        fh.write(s.encode('utf-8'))


def oracles_bullet(H):
    """The Oracles bullet's text in H (its first line up to the next bullet or blank line)."""
    i = H.find(ORA_BULLET_START)
    if i < 0:
        return None
    j = i
    while True:
        k = H.index('\n', j) + 1
        if H.startswith('* ', k) or H.startswith('\n', k):
            return H[i:k]
        j = k


def controls(H):
    C = [('C1-T4-header', '(q : PolyExpr) :\n    ∃ D : Bool → NUPPT',
          '(q : PolyExpr) (hq : 0 < q.eval 0) :\n    ∃ D : Bool → NUPPT'),
         ('C2-T4-statement', '≤ σ κ := by', '< σ κ := by'),
         ('C3-T4-prose', 'negligible `σ` with `|Pr[bb1SimGame',
          'negligible `σ` such that `|Pr[bb1SimGame'),
         ('C4-module-doc', 'This step is its own module so that',
          'This step is a module of its own so that'),
         ('C5-foreign-import', 'import TCSlib.Cryptography.Pairing.Operations\n',
          'import TCSlib.Cryptography.Pairing.Operations\n'
          'import TCSlib.Cryptography.Games.Hopping\n'),
         ('C6-helper-import-misplaced', HP + 'Words\n', HP + 'Words2\n'),
         ('C7-added-decl', END, '\ntheorem extra : True := trivial\n' + END),
         ('C8-main-results', '* `exists_bb1_distinguisher` — the simulation',
          '* `exists_bb1_distinguisher` — this simulation'),
         ('C9a-sketch-spill-blank-line', 'both tuple distributions.\n\n**Proof sketch.**',
          'both tuple distributions.\n**Proof sketch.**'),
         ('C9b-sketch-spill-prose-word', 'both tuple distributions.\n\n**Proof sketch.**',
          'both tuple distribution.\n\n**Proof sketch.**'),
         ('C10a-contents-reword-bullet',
          '* `BonehBoyenMachine.Handler`: the handler and its run.\n',
          '* `BonehBoyenMachine.Handler`: the handler and its runs.\n'),
         ('C10b-contents-extra-bullet', RED, RED + '* `BonehBoyenMachine.Glue`: further glue.\n')]
    bul = oracles_bullet(H)
    if ORA in H and bul is not None:
        C += [('C10b2-contents-second-bullet', bul,
               bul + '* `BonehBoyenMachine.Glue`: further glue.\n'),
              ('C10c-contents-bullet-dropped', bul, ''),
              ('C10d-oracles-import-dropped', ORA, ''),
              ('C11a-oracles-import-after-Reduction', ORA + HP + 'Reduction\n',
               HP + 'Reduction\n' + ORA),
              ('C11b-oracles-import-last', None, None)]
    else:
        for n in ('C10b2-contents-second-bullet', 'C10c-contents-bullet-dropped',
                  'C10d-oracles-import-dropped', 'C11a-oracles-import-after-Reduction',
                  'C11b-oracles-import-last'):
            C.append((n, 'SKIP', None))
    return C


def mutate(H, name, a, b):
    if name == 'C11b-oracles-import-last':
        last = 'import TCSlib.Cryptography.Pairing.Operations\n'
        if H.count(ORA) != 1 or H.count(last) != 1:
            return None
        return H.replace(ORA, '').replace(last, last + ORA)
    if H.count(a) != 1:
        return None
    return H.replace(a, b)


def main(argv):
    if len(argv) < 5:
        print(__doc__)
        return 2
    base, head, chk, out = argv[1:5]
    xa = argv[5:]
    os.makedirs(out, exist_ok=True)
    H = read(head)
    ok = True
    r = subprocess.run([sys.executable, '-I', chk, base, head] + xa, capture_output=True,
                       text=True)
    print('HEAD', 'PASS' if r.returncode == 0 else 'FAIL', '|', (r.stdout + r.stderr).strip())
    ok &= r.returncode == 0
    for name, a, b in controls(H):
        if a == 'SKIP':
            print(name, 'SKIP (head has no Oracles import/bullet)')
            continue
        m = mutate(H, name, a, b)
        if m is None:
            print(name, 'ANCHOR-NOT-UNIQUE (control not applied)')
            ok = False
            continue
        p = os.path.join(out, name + '.lean')
        write(p, m)
        r = subprocess.run([sys.executable, '-I', chk, base, p] + xa, capture_output=True,
                           text=True)
        res = 'FAIL(expected)' if r.returncode != 0 else 'PASS(UNEXPECTED)'
        ok &= r.returncode != 0
        print(name, res, '|', (r.stdout.strip() or r.stderr.strip()).splitlines()[-1][:300])
    print('ALL_CONTROLS_OK', ok)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
