"""sketch_tokens.py <repo> <rev> <out.lean> <out.tsv> (gsw-6b-statements, sub-agent probe; new; check 6 census).
For every theorem of the 9 new files at <rev> whose body is `sorry` (the targets), extract the backticked
identifier-like tokens of its docstring's `**Proof sketch.**` paragraph (tokens with spaces/operators are skipped),
and also the tokens of every definition docstring of the new files (the definitions' bodies are covered by the
Lean census dump). Writes <out.tsv> (file, declaration, token) and <out.lean>, a Lean probe that resolves each
token in the new files' namespace and opens (`ResolveName.resolveGlobalName`), falling back to a suffix search of
the environment (for dot notation on variables such as `Cc.args_lt`), and prints, per token: the resolved
constant(s), kind, module and declaration line, or UNRESOLVED."""
import re, subprocess, sys
repo, rev, outl, outt = sys.argv[1:5]
FILES = ['TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/' + f + '.lean' for f in
         ['Branching', 'DecryptFormula', 'Bootstrap', 'Circular', 'Leveled', 'LeveledSecurity', 'PolyRatio',
          'Asymptotic']] + ['TCSlib/Cryptography/LWE/Ratio.lean']
TOK = re.compile(r"^[A-Za-z_][\w'.₀-₉]*$")
rows = []
for f in FILES:
    src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True).stdout
    for m in re.finditer(r'/--(.*?)-/\s*\n((?:@\[[^\]]*\]\s*\n)?(?:noncomputable\s+)?(theorem|def|abbrev|instance)\s+(\S+)(.*?)(?=\n/--|\n/-!|\nend |\Z))',
                         src, flags=re.S):
        doc, kind, name, rest = m.group(1), m.group(3), m.group(4), m.group(5)
        is_target = kind == 'theorem' and re.search(r':=\s*by\s*\n\s*sorry\s*$', rest.strip() + '\n', flags=re.M) is not None
        part = doc
        if is_target:
            if '**Proof sketch.**' not in doc:
                rows.append((f, name, 'target', '<<NO SKETCH>>')); continue
            part = doc.split('**Proof sketch.**', 1)[1]
        elif kind == 'theorem':
            continue
        for t in re.findall(r'`([^`]+)`', part):
            t = t.strip()
            if TOK.match(t) and not t[0].isdigit():
                rows.append((f, name, 'target' if is_target else kind, t))
with open(outt, 'w') as o:
    for r in rows: o.write('\t'.join(r) + '\n')
toks = sorted({r[3] for r in rows if r[3] != '<<NO SKETCH>>'})
L = ['import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW', 'import TCSlib.Cryptography.LWE', '',
     'open Lean Elab Command', '',
     'def toks : List String := [' + ', '.join('"' + t + '"' for t in toks) + ']', '',
     'def openNs : List Name := [`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW,',
     '  `BoolCircuit, `TCSlib.Cryptography.Encryption.PublicKey, `Complexity,',
     '  `TCSlib.Cryptography, `TCSlib.Cryptography.LWE, `BranchingProgram, `BoolCircuit.FormulaArith]', '',
     '#eval show CommandElabM Unit from do',
     '  let env ← getEnv',
     '  let ns := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW',
     '  let opens := openNs.map fun n => OpenDecl.simple n []',
     '  let all := env.constants.map₁.toList.map (·.1) ++ env.constants.map₂.toList.map (·.1)',
     '  for t in toks do',
     '    let id := t.toName',
     '    let rs0 := (ResolveName.resolveGlobalName env {} ns opens id).filter (·.2.isEmpty) |>.map (·.1)',
     '    let suf := (t.splitOn ".").getLast!',
     '    let (tag, rs) := if !rs0.isEmpty then ("RES", rs0) else',
     '      ("SUF", all.filter fun n => n.toString.endsWith ("." ++ (if t.contains \'.\' && t.front.isLower then suf else t)) && !n.isInternalDetail)',
     '    if rs.isEmpty then IO.println s!"UNRESOLVED\\t{t}" else',
     '    for r in rs.take 4 do',
     '      let ci := (env.find? r).get!',
     '      let k := match ci with | .defnInfo _ => "def" | .thmInfo _ => "thm" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .axiomInfo _ => "axiom" | _ => "other"',
     '      let m := match env.getModuleIdxFor? r with | some i => env.header.moduleNames[i.toNat]! | none => `_',
     '      let ln ← match ← findDeclarationRanges? r with | some d => pure (toString d.selectionRange.pos.line) | none => pure "?"',
     '      IO.println s!"{tag}\\t{t}\\t{r}\\t{k}\\t{m}:{ln}"']
open(outl, 'w').write('\n'.join(L) + '\n')
print(f'{len(rows)} rows, {len(toks)} distinct tokens; targets: {len({(r[0], r[1]) for r in rows if r[2] == "target"})}')
