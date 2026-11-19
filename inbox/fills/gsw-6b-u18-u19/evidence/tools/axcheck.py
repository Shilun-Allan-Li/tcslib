#!/usr/bin/env python3
"""C5 check (gsw-6b-u18-u19): read AxiomProbe's log; every AX line must use only propext,
Classical.choice, Quot.sound, plus sorryAx only for constants whose TRACE names allowed admitted
declarations (the frozen targets of other units the brief names, and through them their own
allowed traces); A1, the public helper and every constant of the owned modules not reaching sorryAx
are standard; no trace may name a declaration of PolyRatio.lean or Asymptotic.lean.
usage: axcheck.py LOG"""
import re, sys
N = 'TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.'
ALLOWED = {N + x for x in [
    # U14-U16 (the brief: bootNoise_le, decrypt_keygen_fheEvalCircuit,
    # decrypt_keygen_leveledEvalCircuit, and through them the U14-U16, U13, U12 targets)
    'bootNoise_le', 'decrypt_keygen_fheEvalCircuit', 'decrypt_keygen_leveledEvalCircuit',
    'encrypts_bootNAND', 'decrypt_fheEval', 'decrypt_fheEvalCircuit', 'encrypts_leveledEval',
    'vecMul_secretVector_eq_sum', 'decryptFormula_eval', 'nandFormula_eval', 'depth_nandFormula_le',
    'maxFanin_nandFormula_le', 'decDepth_le', 'Encrypts.select', 'encrypts_homEvalPBP',
    'encrypts_homEvalFormula',
    # U15-U17 (the brief: distAdv_leveledView_le, and through it distAdv_levelHybrid_le)
    'distAdv_leveledView_le', 'distAdv_levelHybrid_le']}
OWNED_PREFIX = ('PolyRatio', 'Asymptotic')
MUST_STANDARD = {N + 'indCPA_of_dlweAssumption', N + 'Parameters.ofFamily_columns_le'}
STD = {'propext', 'Classical.choice', 'Quot.sound'}
t = open(sys.argv[1]).read()
ax = {}
for l in t.splitlines():
    if l.startswith('AX\t'):
        _, mod, c, s = l.split('\t')
        ax[c] = (mod, set(x.strip() for x in s.strip('[]').split(',') if x.strip()))
trace = {}
for l in t.splitlines():
    if l.startswith('TRACE\t'):
        _, c, s = l.split('\t')
        trace[c] = [x.strip() for x in s.strip('[]').split(',') if x.strip()]
bad = []
owned_names = set(ax)
for c, (mod, s) in sorted(ax.items()):
    extra = s - STD - {'sorryAx'}
    if extra:
        bad.append(f'NONSTANDARD {c} {sorted(extra)}')
    if 'sorryAx' in s:
        if c in MUST_STANDARD:
            bad.append(f'MUST-BE-STANDARD {c}')
        for a in trace.get(c, ['<no trace>']):
            if a not in ALLOWED:
                bad.append(f'TRACE-NOT-ALLOWED {c} -> {a}')
            if a in owned_names:
                bad.append(f'TRACE-NAMES-OWNED {c} -> {a}')
for c in sorted(MUST_STANDARD):
    print(f'{c}: {sorted(ax[c][1]) if c in ax else "MISSING"}')
for c, a in sorted(trace.items()):
    print(f'TRACE {c} -> {a}')
print(f'constants {len(ax)}; sorry-reaching {len(trace)}; standard-only {sum(1 for c in ax if "sorryAx" not in ax[c][1])}')
for b in bad:
    print(b)
print(f'RESULT bad={len(bad)}')
