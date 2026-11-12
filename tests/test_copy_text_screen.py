"""Fixture checks for scripts/copy-text-screen-v4.py: anonymous commands are declaration boundaries.

Each fixture's expected output is the screen's exact stdout, so a change to the row format (which
gate packs cite) also fails here.
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = "tests/fixtures/copy_text_screen"


def screen(*names, version=4):
    files = [f"{FIXTURES}/{n}" for n in names]
    out = subprocess.run(
        [sys.executable, "-I", str(ROOT / f"scripts/copy-text-screen-v{version}.py"), str(ROOT), *files],
        capture_output=True, text=True, check=True,
    )
    return out.stdout.splitlines()


def test_theorem_then_duplicate_example_is_a_pair():
    assert screen("TheoremThenExample.lean") == [
        "declarations screened: 2; copy pairs (target reproduces >= half of source): 2; reproduced text: 184 chars",
        "   TheoremThenExample.lean::<example #1>  reproduces  TheoremThenExample.lean::sum_range_id_mul_two: 92/92 = 100%",
        "   TheoremThenExample.lean::sum_range_id_mul_two  reproduces  TheoremThenExample.lean::<example #1>: 92/102 = 90%",
    ]


def test_v3_hides_the_same_copy_inside_the_theorem():
    # The defect v4 fixes: v3 reads the example as the theorem's body, leaving nothing to compare.
    assert screen("TheoremThenExample.lean", version=3) == [
        "declarations screened: 1; copy pairs (target reproduces >= half of source): 0; reproduced text: 0 chars",
    ]


def test_example_is_paired_with_its_twin_not_the_preceding_theorem():
    # Shaped like quantum E1 Measure.lean at a97fceca (audit findings 1 and 7).
    assert screen("ExampleBeforeTwin.lean") == [
        "declarations screened: 2; copy pairs (target reproduces >= half of source): 2; reproduced text: 216 chars",
        "   ExampleBeforeTwin.lean::length_reverse_cons  reproduces  ExampleBeforeTwin.lean::<example #1>: 108/108 = 100%",
        "   ExampleBeforeTwin.lean::<example #1>  reproduces  ExampleBeforeTwin.lean::length_reverse_cons: 108/108 = 100%",
    ]
    assert screen("ExampleBeforeTwin.lean", version=3)[1:] == [
        "   ExampleBeforeTwin.lean::length_append_reverse  reproduces  ExampleBeforeTwin.lean::length_reverse_cons: 108/108 = 100%",
    ]


def test_anonymous_instances_and_examples_get_synthetic_names():
    # `<example #2>`: the short first example is not screened but still counts; instances stay terms
    # and examples are proofs, so no instance is paired with an example or theorem.
    assert screen("Instances.lean") == [
        "declarations screened: 5; copy pairs (target reproduces >= half of source): 8; reproduced text: 532 chars",
        "   Instances.lean::<example #2>  reproduces  Instances.lean::box_val_zero: 62/62 = 100%",
        "   Instances.lean::instBoxNonempty  reproduces  Instances.lean::<instance #2>: 68/69 = 99%",
        "   Instances.lean::instBoxNonempty  reproduces  Instances.lean::<instance #1>: 68/69 = 99%",
        "   Instances.lean::<instance #2>  reproduces  Instances.lean::<instance #1>: 68/69 = 99%",
        "   Instances.lean::<instance #1>  reproduces  Instances.lean::<instance #2>: 68/69 = 99%",
        "   Instances.lean::<instance #2>  reproduces  Instances.lean::instBoxNonempty: 68/71 = 96%",
        "   Instances.lean::<instance #1>  reproduces  Instances.lean::instBoxNonempty: 68/71 = 96%",
        "   Instances.lean::box_val_zero  reproduces  Instances.lean::<example #2>: 62/72 = 86%",
    ]


def test_synthetic_names_are_per_file_and_files_screen_together():
    lines = screen("TheoremThenExample.lean", "ExampleBeforeTwin.lean")
    assert lines[0].startswith("declarations screened: 4;")
    assert "   ExampleBeforeTwin.lean::<example #1>  reproduces  ExampleBeforeTwin.lean::length_reverse_cons: 108/108 = 100%" in lines
    assert "   TheoremThenExample.lean::<example #1>  reproduces  TheoremThenExample.lean::sum_range_id_mul_two: 92/92 = 100%" in lines
