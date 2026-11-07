"""G08-04 lexical regressions; run from the campaign root with python3 -I."""
from pathlib import Path
import runpy

root = Path.cwd()
gate = root / "briefs/pass-shelat-ch5-8/gates/08-shared"
api = runpy.run_path(str(gate / "evidence/tools/sorrycensus.py"), run_name="census_api")
cases = [
    ("sorry", 1),
    ('"declaration uses \'sorry\'"', 0),
    ("/- outer /- sorry -/ sorry -/ sorry", 1),
    ("-- sorry\nsorry", 1),
    ('"escaped \\" sorry" sorry', 1),
    ('r##"sorry \\" sorry"## sorry', 1),
    ("«sorry» sorryAx sorry' A.sorry sorry", 1),
]
lines = []
for source, expected in cases:
    actual = api["count"](source)
    assert actual == expected, (source, actual, expected)
    lines.append(f"PASS {source!r}: {actual}")
lines.append(f"PASS {len(cases)} lexical regression cases")
(gate / "evidence-r2/census-regressions.log").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
