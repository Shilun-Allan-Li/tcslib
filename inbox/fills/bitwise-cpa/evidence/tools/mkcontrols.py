# Seal controls of the bitwise-cpa fill: readings through definition bodies that must pass
# unsealed and fail when the full candidate list is sealed.
F = '/home/user/fill'
cands = [l.strip() for l in open(F + '/evidence/seal/candidates.txt') if l.strip()]
body = '''open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.ChallengeSim
open TCSlib.Cryptography.Composability.BitwiseSim

-- Control 1: `FixedLengthPKScheme.inLens` through its body.
example (S : FixedLengthPKScheme) (n : ℕ) :
    S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl
-- Control 2: `FixedLengthPKScheme.outLens` through its body.
example (S : FixedLengthPKScheme) (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl
-- Control 3: `PolyExpr.eval` through its body.
example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
-- Control 4: `padCt` through its body.
example (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl
-- Control 5: `seedIn` through its body.
example (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) := rfl
-- Control 6: the published helper `chRun` through its body.
example {ins outs : Fin 2 → ℕ} (g : (Fin (ins 1) → Bool) → List Bool) (a : ℕ)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl
-- Control 7: the new helper `qDin` through its body.
example (Lc Lq : PolyExpr) : qDin Lc Lq 1 = Lq := rfl
-- Control 8: the new helper `plantAns` through its body.
example (Enc : NUPPT) (L : PolyExpr) (w : List Bool) :
    plantAns Enc L w = padCt (L.eval (pairFstD (pairFstD w)).length) (plantTuple Enc w) := rfl
'''
imp = 'import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA\n\n'
open(F + '/evidence/seal/SealControlsUnsealed.lean', 'w').write(imp +
  '/-! Seal controls of the bitwise-cpa fill (unsealed: every example must pass): eight readings\nthrough a definition body. -/\n\n' + body)
open(F + '/evidence/seal/SealControlsSealed.lean', 'w').write(imp +
  '/-! Seal controls of the bitwise-cpa fill (sealed with the full candidate list: every example\nmust fail): eight readings through a definition body. -/\n\n' +
  'attribute [local irreducible] ' + ' '.join('_root_.' + c for c in cands) + '\n\n' + body)
print(len(cands), 'candidates')
