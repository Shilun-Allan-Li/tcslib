"""Check comment-stripped source signatures and definition bodies against phase 0.

Reuse the repository's nesting-aware comment stripper. Ignore theorem proof bodies,
but retain every signature, definition/instance body, structure, attribute and namespace.
The sole allowed import addition is the public list-slicing lemma's Mathlib owner.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = "4364d0e0fe9accd649b6acb4751e8684aa93ad1e"
GATE = ROOT / "briefs/lwe-sis-constructions/gates/00-foundations/evidence"
STRIP = runpy.run_path(str(ROOT / "scripts/campaign_style_lint.py"))["strip_comments"]
COMMAND = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|theorem|lemma|instance|structure|class|inductive|abbrev|axiom|opaque|"
    r"namespace|end|attribute|variable|open|set_option|import)\b", re.M)
DECL = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(def|theorem|lemma|instance|structure|class|inductive|abbrev|axiom|opaque)\b\s*(.*)")


def outer_assignment(text):
    stack = []
    pairs = {"(": ")", "[": "]", "{": "}"}
    for position, char in enumerate(text):
        if char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif not stack and text.startswith(":=", position):
            return position
    raise AssertionError("Theorem has no outer proof assignment")


def inspect(text):
    text = STRIP(text)
    starts = list(COMMAND.finditer(text))
    output, declarations, proofs, namespaces = [], [], {}, []
    output.append(text[:starts[0].start()] if starts else text)
    for index, start in enumerate(starts):
        stop = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        block = text[start.start():stop]
        first = block.splitlines()[0]
        if first.startswith("namespace "):
            namespaces.append(first.split()[1])
        elif first == "end" or first.startswith("end "):
            namespaces.pop()
        match = DECL.match(first)
        if match:
            kind, tail = match.groups()
            name = ("instNeZeroNatModulus" if kind == "instance"
                    else re.match(r"[^\s(:{]+", tail).group(0))
            full = ".".join([*namespaces, name])
            declarations.append((kind, full))
            if kind in {"theorem", "lemma"}:
                assignment = outer_assignment(block)
                proofs[full] = " ".join(block[assignment + 2:].split())
                block = block[:assignment + 2] + " <proof>\n"
        output.append(block)
    return " ".join("".join(output).split()), declarations, proofs


def main():
    source = json.loads((GATE / "source-declarations.json").read_text())
    targets = {row["name"] for row in json.loads((GATE / "admissions.json").read_text())}
    files = {row["module"] + ".lean" for row in source}
    files.update("TCSlib/Cryptography/" + name + ".lean"
                 for name in ["Encoding", "LWE", "SIS"])
    all_before, all_after, changed, records = [], [], set(), []
    added_import = "import Mathlib.Algebra.BigOperators.Group.List.Lemmas\n"
    for path in sorted(files):
        before = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=ROOT).decode()
        after = (ROOT / path).read_text()
        compared_after = after
        if path == "TCSlib/Cryptography/SIS/Encoding.lean":
            assert added_import not in before and after.count(added_import) == 1
            compared_after = after.replace(added_import, "", 1)
        old_surface, old_decls, old_proofs = inspect(before)
        new_surface, new_decls, new_proofs = inspect(compared_after)
        assert old_surface == new_surface, "Signature/definition/instance drift: " + path
        assert old_decls == new_decls, "Ordered declaration drift: " + path
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", STRIP(after)), path
        all_before += old_decls
        all_after += new_decls
        changed.update(name for name in old_proofs if old_proofs[name] != new_proofs[name])
        records.append(dict(path=path, source_sha256=hashlib.sha256(after.encode()).hexdigest(),
                            invariant_surface_sha256=hashlib.sha256(new_surface.encode()).hexdigest()))
    assert all_before == all_after and len(all_after) == 61
    assert Counter(all_before) == Counter(all_after)
    assert changed == targets and len(changed) == 14, changed ^ targets
    unchanged = []
    freeze = json.loads((GATE / "source-freeze.json").read_text())
    for row in freeze["files"]:
        if row["path"] not in files:
            assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]
            unchanged.append(row["path"])
    result = dict(baseline=BASE, source_declarations_before=len(all_before),
                  source_declarations_after=len(all_after),
                  ordered_declarations_unchanged=True, declaration_multiset_unchanged=True,
                  signatures_definitions_instances_attributes_namespaces_unchanged=True,
                  changed_proof_bodies=sorted(changed), new_helpers=0,
                  added_import=added_import.strip(), unchanged_frozen_files=unchanged,
                  source_files=records,
                  scope="Comment-stripped source invariant; this is not a claim of elaborated type-hash comparison.")
    evidence = HERE / "evidence"
    evidence.mkdir(exist_ok=True)
    (evidence / "freeze-attestation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"declarations": len(all_after), "proved_targets": len(changed),
                      "unchanged_other_frozen_files": len(unchanged), "signature_definition_drift": False}))


if __name__ == "__main__":
    main()
