"""Paired Rule 10 controls for the gsw-security seals.

Each control is a small Lean file with the owned file's imports. A *positive* control reads a
foreign definition through its published reader; it must pass unsealed and in every sealed
variant. A *negative* control reads the same definition through its body (`rfl`); it must
pass unsealed and fail **exactly once** in every variant that seals the definition. Each
negative is alone in its file, so its sealed error count is that one declaration's.
Rows whose definition a variant exempts (projection coercions in `coe`, `PolyExpr.eval` in A)
are expected to pass in that variant.

Usage (python3 -I, from the fill checkout root): make_controls.py <phase> <set>
  <set> = columns   (imports of Columns.lean; checkpoint 1)
        = security  (imports of Security.lean; final)
Writes probes/controls/<phase>/{src,sealed}/, manifest.json (with `expected`), order.txt.
"""
import json
from pathlib import Path
import runpy
import sys

seal = runpy.run_path(str(Path(__file__).with_name('make_seals.py')))
phase, which = sys.argv[1], sys.argv[2]

COLUMNS_HEAD = '''import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

namespace TCSlib.Cryptography.Hashing.SIS
open TCSlib.Cryptography.SIS (Parameters)
'''
COLUMNS_TAIL = '\nend TCSlib.Cryptography.Hashing.SIS\n'
SECURITY_HEAD = '''import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey
'''
SECURITY_TAIL = '\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW\n'

HASH = ('TCSlib.Cryptography.Hashing.SIS.hash',
        '''example (P : Parameters) (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (x : Fin P.columns → Bool) :
    hash P A x = A.mulVec (fun i => ((x i).toNat : ZMod P.modulus)) := BODY
''', 'hash_eq P A x')
DISTADV = ('TCSlib.Cryptography.distAdv',
           '''example {σ τ γ ρ : Type} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = |acceptProb X D - acceptProb Y D| := BODY
''', 'distAdv_def X Y D')
ACCEPT = ('TCSlib.Cryptography.acceptProb',
          '''example {σ γ ρ : Type} [Fintype σ] [Fintype ρ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X D = uprob fun z : σ × ρ => D (X z.1) z.2 = true := BODY
''', 'acceptProb_def X D')
FINDIST = ('TCSlib.InformationTheory.FinDist instCoeFun (projection coercion)',
           '''example {α : Type} [Fintype α] (p : TCSlib.InformationTheory.FinDist α) (a : α) :
    p a = p.prob a := BODY
''', None)
HASHCOLS = ('TCSlib.Cryptography.Hashing.SIS.hashColumns',
            '''example (P : TCSlib.Cryptography.SIS.Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) (i : Fin P.dimension) (j : Fin N) :
    Hashing.SIS.hashColumns P N A R i j = Hashing.SIS.hash P A (fun c => R c j) i := BODY
''', 'Hashing.SIS.hashColumns_apply P N A R i j')
AUGMENTED = ('TCSlib.Cryptography.Encryption.PublicKey.Regev.augmented',
             '''example (P : LWE.Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    Regev.augmented P pk = Fin.snoc pk.1.transpose pk.2 := BODY
''', 'Regev.augmented_eq P pk')
SAMPLE = ('TCSlib.Cryptography.LWE.sample',
          '''example (P : LWE.Parameters) (χ : LWE.Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (LWE.sample P χ r).1 = r.1 := BODY
''', 'LWE.sample_fst P χ r')
ENCRYPT = ('TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encrypt',
           '''example (P : Parameters)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Bool) (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    encrypt P pk μ R =
      Regev.augmented P.lwe pk * lift P R + (μ.toNat : ZMod P.lwe.modulus) • gadget P := BODY
''', 'encrypt_eq P pk μ R')
POLYEVAL = ('Complexity.PolyExpr.eval (notation; exempt in A, sealed in B)',
            '''example (n : ℕ) : Complexity.PolyExpr.eval (Complexity.PolyExpr.const 3) n = 3 := BODY
''', None)

SETS = {
    'columns': (COLUMNS_HEAD, COLUMNS_TAIL, [('hash', HASH), ('distAdv', DISTADV),
                                             ('acceptProb', ACCEPT), ('finDistCoe', FINDIST)]),
    'security': (SECURITY_HEAD, SECURITY_TAIL, [('hashColumns', HASHCOLS),
                                                ('augmented', AUGMENTED), ('sample', SAMPLE),
                                                ('encrypt', ENCRYPT), ('distAdv', DISTADV),
                                                ('finDistCoe', FINDIST),
                                                ('polyEval', POLYEVAL)]),
}
head, tail, rows = SETS[which]
out = Path('probes/controls') / phase
(out / 'src').mkdir(parents=True, exist_ok=True)
(out / 'sealed').mkdir(parents=True, exist_ok=True)
manifest = []


def expected_sealed(key, mode, coe, negative):
    if not negative:
        return 0
    if key == 'finDistCoe' and coe:
        return 0
    if key == 'polyEval' and mode == 'A':
        return 0
    return 1


for key, (target, template, reader) in rows:
    for negative in ([False, True] if reader else [True]):
        kind = 'neg' if negative else 'pos'
        body = 'rfl' if negative else reader
        src = head + '\n' + template.replace('BODY', body) + tail
        stem = f'Ctl_{key}_{kind}'
        unsealed = out / 'src' / f'{stem}.lean'
        unsealed.write_text(src)
        manifest.append(dict(control=key, target=target, kind=kind, variant='unsealed',
                             probe=str(unsealed), expected=0))
        for mode in ['A', 'B']:
            for coe in [False, True]:
                variant = f'{mode}_{"coe" if coe else "strict"}'
                label = f'{phase}_{stem}_{variant}'
                probe, mapping, offset = seal['prepare'](src, label, mode, coe)
                dest = out / 'sealed' / f'{stem}_{variant}.lean'
                dest.write_text(probe)
                dest.with_suffix('.linemap.json').write_text(json.dumps(mapping) + '\n')
                manifest.append(dict(control=key, target=target, kind=kind, variant=variant,
                                     probe=str(dest), label=label, mode=mode, coe=coe,
                                     expected=expected_sealed(key, mode, coe, negative)))
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Prepared {len(manifest)} control probes under {out}')
