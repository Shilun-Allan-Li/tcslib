"""Publish records-only proof-audit intake to the existing draft PR.

No exchange or campaign ref is updated. No merge, force, reset or stash is performed.
"""

import hashlib
import json
from pathlib import Path
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TOPIC = "cryptography/lwe-sis-encoding-proofs"
TARGET = "cryptography/pass-shelat-ch2-4"
REPO = "Shilun-Allan-Li/tcslib"
SOURCE = "893e921bf2afeca293be9da9d495613bb1486796"
PRE_INTAKE = "aaf4d1d3ea2e5113b6f53c3fedd9b5d47e852de1"
ALLOWED = {
    "LatticeCryptographyPlan.md",
    "audits/lwe-sis-encoding-proofs-findings.md",
    "audits/lwe-sis-encoding-proofs-resolutions.md",
    "briefs/lwe-sis-constructions/README.md",
    "briefs/lwe-sis-constructions/fills/00-encodings/intake-r1.json",
    "briefs/lwe-sis-constructions/fills/00-encodings/intake-r1-pr-body.md",
    "briefs/lwe-sis-constructions/fills/00-encodings/publish_intake.py",
}


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()


def main():
    assert shutil.which("gh"), "GitHub CLI is required to update the PR description."
    assert Path(git("rev-parse", "--show-toplevel")) == ROOT
    assert git("branch", "--show-current") == TOPIC
    assert not git("status", "--porcelain"), "The own PR checkout must be clean."
    assert git("remote", "get-url", "--push", "--all", "origin") == (
        "https://github.com/" + REPO + ".git")
    subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor", PRE_INTAKE, "HEAD"],
                   check=True)
    changed = set(git("diff", "--name-only", "--no-renames", PRE_INTAKE, "HEAD").splitlines())
    assert changed == ALLOWED, "Unexpected intake paths: " + repr(changed ^ ALLOWED)
    assert not git("diff", "--name-only", SOURCE, "HEAD", "--", "TCSlib", "TCSlib.lean",
                   "lean-toolchain", "lake-manifest.json")
    receipt = json.loads((HERE / "intake-r1.json").read_text())
    report = (ROOT / receipt["report_path"]).read_bytes()
    assert len(report) == receipt["report_bytes"]
    assert hashlib.sha256(report).hexdigest() == receipt["report_sha256"]

    def gh(*args):
        return subprocess.check_output(["gh", *args], cwd=ROOT, text=True).strip()

    pr = json.loads(gh("pr", "view", "236", "--repo", REPO, "--json",
                       "headRefName,baseRefName,state,isDraft,url"))
    assert pr["headRefName"] == TOPIC and pr["baseRefName"] == TARGET
    assert pr["state"] == "OPEN" and pr["isDraft"], "Inspect the PR state before publication."
    head = git("rev-parse", "HEAD")
    subprocess.run(["git", "-C", str(ROOT), "push", "--no-follow-tags", "origin",
                    head + ":refs/heads/" + TOPIC], check=True)
    gh("pr", "edit", "236", "--repo", REPO, "--body-file", str(HERE / "intake-r1-pr-body.md"))
    print("Published audit-intake records: " + head)
    print("Draft PR: " + pr["url"])
    print("No exchange/campaign ref was updated; no merge was performed.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit("Publication stopped after exit " + str(error.returncode)
                         + "; no force or merge was attempted.") from None
