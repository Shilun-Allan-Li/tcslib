"""mkcensus.py <side: head|base> <modules file> <namemap> <out.lean>: a census probe module.
For every stored constant whose home module is one of <modules>: normalized name (private prefix
stripped), home, kind, type hash after renaming every constant to its normalized name (and, on the
base side, through the name map old -> new), reducibility, simp, instance, protected, axioms.
Also #print axioms of the campaign endpoints."""
import sys, re
side, modsf, nmap, out = sys.argv[1:5]
mods = [l.strip().replace('/', '.') for l in open(modsf) if l.strip()]
pairs = []
for l in open(nmap):
    l = l.strip()
    if not l or l.startswith('#'): continue
    a, b = [x.strip() for x in l.split('->')]
    if a == '-' or a == b: continue
    a = re.sub(r'^_private\.[^ ]*?\.0\.', '', a)
    pairs.append((a, b))
endpoints = '''TCSlib.Cryptography.Composability.prfFixedScheme_cpa
TCSlib.Cryptography.Composability.prfFixedScheme_cca1
TCSlib.Cryptography.Composability.not_prfFixedScheme_cca2
TCSlib.Cryptography.Composability.prfFixedScheme_not_cca2
TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa
TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa
TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_rsa
TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_factoring
TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2
TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_of_nmSecure_cca2
TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2'''.split()
L = ['import Lean'] + [f'import {m}' for m in mods] + ['import TCSlib.Cryptography.Implications.PublicKey', '',
     f'/-! dl-consolidation review census probe ({side} side). -/', '', 'set_option maxHeartbeats 0',
     'set_option maxRecDepth 65536', '', 'open Lean Elab Command', '']
L += [f'#print axioms {e}' for e in endpoints] + ['']
L.append('def owners : List Name := [' + ',\n  '.join('`' + m for m in mods) + ']')
L.append('def nameMap : Std.HashMap String String := Std.HashMap.ofList [' +
         (',\n  '.join(f'("{a}", "{b}")' for a, b in pairs) if side == 'base' else '') + ']')
L.append(r'''
def normName (n : Name) : String := ((Lean.privateToUserName? n).getD n).toString

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def abbrevOf : ConstantInfo → String
  | .defnInfo d => (match d.hints with | .abbrev => "abbrev" | _ => "-")
  | _ => "-"

def renameE (e : Expr) : Expr := e.replace fun x => match x with
  | .const n ls =>
    let s := normName n
    some (.const (Name.mkSimple ((nameMap[s]?).getD s)) ls)
  | _ => none

run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let simps := Lean.Meta.simpExtension.getState env
  let mut n := 0
  for (c, ci) in env.constants.toList do
    let some mi := env.getModuleIdxFor? c | continue
    let home := names[mi.toNat]!
    unless owners.contains home do continue
    let axs ← liftCoreM (Lean.collectAxioms c)
    let axs := (axs.map (·.toString)).qsort (· < ·)
    let red := match Lean.getReducibilityStatusCore env c with
      | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
    let abbr := abbrevOf ci
    IO.println s!"C\t{normName c}\t{c.isInternal || (Lean.privateToUserName? c).isSome}\t{(Lean.privateToUserName? c).isSome}\t{home}\t{kindOf ci}\t{(renameE ci.type).hash}\t{red}\t{abbr}\t{simps.isLemma (.decl c)}\t{Lean.Meta.isInstanceCore env c}\t{isProtected env c}\t{axs.toList}"
    n := n + 1
  IO.println s!"C-COUNT {n}"
''')
open(out, 'w').write('\n'.join(L) + '\n')
