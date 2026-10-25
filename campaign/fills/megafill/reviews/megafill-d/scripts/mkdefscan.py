"""Make a def-scan probe from a route-probe record: insert `import Lean` after the header comment
(before the first import) and append a command that lists, for the given root declarations, every
TCSlib *definition* that appears in the type or value of a root or of any declaration of this file
the roots reach (imported declarations are not entered). Usage: mkdefscan.py <record> <out> <root>..."""
import sys
src, out, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
text = open(src).read()
i = text.index("\nimport ")
assert text.count("import Lean\n") == 0
text = text[: i + 1] + "import Lean\n" + text[i + 1 :]
roots_lean = ", ".join(f"`{r}" for r in roots)
text += f"""

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut todo : Array Name := #[{roots_lean}]
  let mut seen : NameSet := {{}}
  let mut found : Array String := #[]
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    match env.getModuleIdxFor? n with
    | none =>
      for c in ci.type.getUsedConstants do todo := todo.push c
      if let some v := ci.value? then
        for c in v.getUsedConstants do todo := todo.push c
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if (`TCSlib).isPrefixOf mod then
        if let .defnInfo _ := ci then
          found := found.push s!"{{n}} ({{mod}})"
  for s in found.qsort (· < ·) do IO.println s!"DEF {{s}}"
"""
open(out, "w").write(text)
print("wrote", out)
