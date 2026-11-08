"""Parse retained, established Lean metadata formats without executing payloads."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def dump(name, obj):
    (OUT / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def axes(raw):
    return [s.strip() for s in raw.split(",") if s.strip()]


def unique(rows, key):
    result = {}
    for row in rows:
        name = row[key]
        assert name not in result, ("duplicate", name)
        result[name] = row
    return result


def census(text):
    rows = []
    for m in re.finditer(r"^CONSTANT (\S+) module=(\S+) kind=(\S+) private=(true|false) internal=(true|false)$", text, re.M):
        n, owner, kind, private, internal = m.groups()
        rows.append(dict(name=n, module=owner, kind=kind,
                         private=private == "true", internal=internal == "true"))
    return unique(rows, "name")


def axmap(text, tag):
    rows = []
    for m in re.finditer(r"^" + re.escape(tag) + r"\|([^|\n]+)\|\[([^\]]*)\]", text, re.M):
        n, raw = m.groups()
        rows.append(dict(name=n, axioms=axes(raw)))
    return unique(rows, "name")


raw_path = OUT / "Metadata-roots-census-v1.out"
raw = raw_path.read_text()
constants = census(raw)
owners = (OUT / "original9-owners.txt").read_text().splitlines()
assert set(r["module"] for r in constants.values()) == set(owners)
roots = unique([dict(name=m[1], private=m[2] == "true") for m in
                re.finditer(r"^ROOT\|([^|\n]+)\|private=(true|false)$", raw, re.M)], "name")
assert len(roots) == 16 and all(r["private"] for r in roots.values())
expected = json.loads((OUT / "combined16.json").read_text())
expected_pairs = {(r["source_name"], r["owner"]) for r in expected}
assert {(n.rsplit(".", 1)[-1], constants[n]["module"]) for n in roots} == expected_pairs
proofs = unique([dict(name=m[1], kind=m[2], axioms=axes(m[3])) for m in
                 re.finditer(r"^PROOFAX\|([^|\n]+)\|kind=([^|\n]+)\|\[([^\]]*)\]", raw, re.M)], "name")
selected_names = {n for n in constants if any(n == r or n.startswith(r + ".") for r in roots)}
assert set(proofs) == selected_names
assert all(set(p["axioms"]) <= STANDARD for p in proofs.values())
assert all(proofs[n]["kind"] == constants[n]["kind"] for n in proofs)
for n in roots:
    assert constants[n]["kind"] == "theorem"
    roots[n].update(owner=constants[n]["module"], kind=constants[n]["kind"],
                    axioms=proofs[n]["axioms"],
                    descendants=sorted(x for x in proofs if x.startswith(n + ".")))

cited = []
for m in re.finditer(r"^CITED\|([^|\n]+)\|([^|\n]+)\|([^|\n]+)\|kind=([^|\n]+)\|private=(true|false)$", raw, re.M):
    root, n, owner, kind, private = m.groups()
    assert root in proofs
    cited.append(dict(root=root, name=n, owner=owner, kind=kind,
                      private=private == "true", same_home=owner == constants[root]["module"]))
assert len({(x["root"], x["name"]) for x in cited}) == len(cited)
foreign_private = [x for x in cited if x["private"] and not x["same_home"]]
definitions = []
for m in re.finditer(r"^FOREIGNDEF\|([^|\n]+)\|([^|\n]+)\|([^|\n]+)\|hints=(\S+)$", raw, re.M):
    root, n, owner, hints = m.groups()
    assert root in proofs
    definitions.append(dict(root=root, name=n, owner=owner, hints=hints,
                            same_home=owner == constants[root]["module"]))

all_path = OUT / "Metadata-whole9-axioms-v1.out"
all_raw = all_path.read_text()
all_axioms = axmap(all_raw, "ALLAX")
public_axioms = axmap(all_raw, "PUBLICAX")
assert set(all_axioms) == set(constants), (len(all_axioms), len(constants))
assert set(public_axioms) == {n for n, c in constants.items() if not c["private"]}
assert all(public_axioms[n] == all_axioms[n] for n in public_axioms)
assert all(proofs[n]["axioms"] == all_axioms[n]["axioms"] for n in proofs)
nonstandard = {n: dict(**constants[n], axioms=r["axioms"],
                       nonstandard_axioms=sorted(set(r["axioms"]) - STANDARD))
               for n, r in all_axioms.items() if set(r["axioms"]) - STANDARD}
owner_counts = {}
for owner in owners:
    members = [x for x in constants.values() if x["module"] == owner]
    owner_counts[owner] = dict(total=len(members), private=sum(x["private"] for x in members),
                               nonprivate=sum(not x["private"] for x in members),
                               kinds=dict(sorted(Counter(x["kind"] for x in members).items())),
                               nonstandard_axioms=sum(x["name"] in nonstandard for x in members))

dump("compiled-census.json", constants)
dump("repair-roots.json", roots)
dump("compiled-proof-axioms.json", proofs)
dump("compiled-direct-citations.json", cited)
dump("compiled-definition-citations.json", definitions)
dump("compiled-whole9-axioms.json", all_axioms)
dump("compiled-whole9-public-axioms.json", public_axioms)
dump("compiled-whole9-nonstandard-axioms.json", nonstandard)
summary = dict(
    context="MSG4 pre-#230 complete dependencies; exact final SAT/Hardness compiled into own overlay",
    raw_inputs={p.name: dict(bytes=p.stat().st_size, sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                for p in [raw_path, all_path]},
    census_constants=len(constants), private=sum(x["private"] for x in constants.values()),
    nonprivate=sum(not x["private"] for x in constants.values()),
    owners=owner_counts, repaired_roots=len(roots), generated_descendants=len(proofs) - len(roots),
    selected_standard_axioms=True, selected_sorryAx=False,
    ALLAX_exact_census_coverage=True, PUBLICAX_exact_nonprivate_coverage=True,
    selected_AX_agree_across_both_probes=True,
    whole9_nonstandard_constants=len(nonstandard),
    whole9_nonstandard_axiom_kinds=sorted({a for x in nonstandard.values() for a in x["nonstandard_axioms"]}),
    direct_citations=len(cited), same_home_private_citations=sum(x["private"] and x["same_home"] for x in cited),
    different_home_private_citations=foreign_private,
    direct_cited_homes=sorted({x["owner"] for x in cited}),
    direct_different_home_ordinary_definitions=sorted({x["name"] for x in definitions if x["hints"] == "regular" and not x["same_home"]}),
    limitations=["This is compiled metadata, not an additional seal run.",
                 "No claim that unchanged legacy proofs are sealed or sorry-free.",
                 "Private compiler identifiers are retained exactly; none are normalized.",
                 "CITED inspects direct root/descendant type and value references, not recursive bodies; axiom collection is transitive.",
                 "Same-home private helpers are distinguished from private constants owned by other modules.",
                 "No current merged-tree replay or current post-#230 whole-tree census is claimed."])
dump("metadata-summary.json", summary)
print(json.dumps({k: summary[k] for k in ["census_constants", "private", "nonprivate", "repaired_roots", "generated_descendants", "selected_standard_axioms", "whole9_nonstandard_constants", "whole9_nonstandard_axiom_kinds", "same_home_private_citations", "different_home_private_citations"]}, indent=2))
