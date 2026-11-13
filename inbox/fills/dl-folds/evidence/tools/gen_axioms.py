#!/usr/bin/env python3
"""Write scratch/census/AxFinal.lean: imports of every module of ORDER, then the axioms of every
stored constant of the MODULES list (`AX` lines) and of the campaign endpoints (`ENDPOINT` lines).
usage: gen_axioms.py ORDER MODULES"""
import sys
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
mods = [l.strip() for l in open(sys.argv[2]) if l.strip()]
EP = ['TCSlib.Cryptography.Composability.prfFixedScheme_cpa',
      'TCSlib.Cryptography.Composability.prfFixedScheme_cca1',
      'TCSlib.Cryptography.Composability.not_prfFixedScheme_cca2',
      'TCSlib.Cryptography.Composability.prfFixedScheme_not_cca2',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa',
      'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa',
      'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa',
      'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa',
      'TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_rsa',
      'TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_factoring',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_of_nmSecure_cca2',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmSecure_of_simNMSecure',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa',
      'TCSlib.Cryptography.Composability.FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa']
out = ['import ' + m.replace('/', '.') for m in order]
out.append('''
open Lean Elab Command

/-! Axioms of every stored constant of the dl-folds changed and new modules, and of the campaign
endpoints. One `AX` / `ENDPOINT` line each. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [%s]
  let mut out : Array String := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    let axs ← liftCoreM <| collectAxioms c
    let axs := (axs.map toString).qsort (· < ·)
    out := out.push s!"AX\\t{mod}\\t{c}\\t{axs.toList}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size}"
  for e in [%s] do
    if env.contains e then
      let axs ← liftCoreM <| collectAxioms e
      let axs := (axs.map toString).qsort (· < ·)
      IO.println s!"ENDPOINT {e}: {axs.toList}"
    else IO.println s!"ENDPOINT {e}: MISSING"
''' % (', '.join('`' + m.replace('/', '.') for m in mods), ', '.join('`' + e for e in EP)))
open('/workspace/folds/scratch/census/AxFinal.lean', 'w').write('\n'.join(out) + '\n')
print(len(order), 'imports;', len(mods), 'modules;', len(EP), 'endpoints')
