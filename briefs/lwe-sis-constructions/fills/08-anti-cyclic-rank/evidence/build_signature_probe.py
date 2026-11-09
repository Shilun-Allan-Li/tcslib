"""Generate reflexivity certificates for elaborated types that change representation."""
import argparse
import json
from pathlib import Path
import textwrap


def types(path):
    result = {}
    for line in path.read_text().splitlines():
        if line.startswith("RAW_TYPE|"):
            name, levels, expression = json.loads(line.split("|", 1)[1])
            assert name not in result
            result[name] = (levels, expression)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("current", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    before, after = types(args.baseline), types(args.current)
    assert len(before) == 220 and before.keys() == after.keys()
    names = sorted(name for name in before if before[name] != after[name])
    expected = {
        "antiCyclic_mulVec_injective", "branch_difference_injective", "branch_message_bound",
        "residual_branch",
    }
    prefix = "TCSlib.Cryptography.TrapdoorFunctions.AllButOne."
    assert set(names) == {prefix + name for name in expected}
    body = [
        "import TCSlib.Cryptography.TrapdoorFunctions",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 2048",
        "",
        "open Lean Elab Command",
        "",
    ]
    for index, name in enumerate(names):
        levels, expression = before[name]
        assert levels == after[name][0] == "[]", name
        # The repr prints this hygienic binder name with an unescaped component.
        # Spell its exact Name constructors so the archived Expr parses.
        hygienic_name = "a._@._internal._hyg"
        encoded_name = "Lean.Name.anonymous"
        for component in hygienic_name.split("."):
            encoded_name = f"(Lean.Name.str {encoded_name} {json.dumps(component)})"
        expression = expression.replace("`" + hygienic_name, encoded_name)
        body.extend([
            f"private def previousType{index} : Lean.Expr :=",
            textwrap.indent(expression, "  "),
            "",
        ])
    body.append("run_cmd do")
    body.append("  liftTermElabM do")
    for index, name in enumerate(names):
        body.extend([
            f"    let current{index} ← getConstInfo `{name}",
            f"    let equality{index} ← Meta.mkEq previousType{index} current{index}.type",
            f"    let reflexivity{index} ← Meta.mkEqRefl previousType{index}",
            "    addDecl (.thmDecl {",
            f"      name := `rankTypePreserved{index}",
            f"      levelParams := current{index}.levelParams",
            f"      type := equality{index}",
            f"      value := reflexivity{index} }})",
            f'    logInfo "KERNEL_TYPE_EQ|{name}"',
        ])
    args.output.write_text("\n".join(body) + "\n")


if __name__ == "__main__":
    main()
