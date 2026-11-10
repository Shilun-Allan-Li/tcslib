"""Publish this draft and pinned review inputs with client Git/GitHub credentials.

Only the draft code ref and owned exchange namespace are pushed. No merge is performed.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REPO = "Shilun-Allan-Li/tcslib"
REMOTE = "https://github.com/" + REPO + ".git"
TOPIC = "cryptography/lwe-sis-adapter-statements"
CENTRAL = "cryptography/lwe-sis-constructions"
EXCHANGE = "exchange/pass-shelat-ch5-8"
SOURCE = "6eec97be8f54d9990340900a5595dab32fb477f5"


def git(checkout, *args, capture=True):
    result = subprocess.run(["git", "-C", str(checkout), *args],
                            capture_output=capture, text=True, check=True)
    return result.stdout.strip() if capture else ""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", choices=["codex", "claude"])
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    assert args.check_only or args.worker, "Select Codex or Claude explicitly for this job."
    record = json.loads((HERE / "review-publication.json").read_text())
    publisher = Path(record["publisher_checkout"])
    assert publisher.name == "tcslib-exchange-lwe-sis-publish" and (publisher / ".git").is_dir()
    assert Path(git(ROOT, "rev-parse", "--show-toplevel")) == ROOT
    assert git(ROOT, "branch", "--show-current") == TOPIC
    assert not git(ROOT, "status", "--porcelain"), "The own PR checkout must be clean."
    assert git(ROOT, "remote", "get-url", "--push", "--all", "origin") == REMOTE
    assert record["source_pin"] == SOURCE
    assert not git(ROOT, "diff", "--name-only", SOURCE, "HEAD", "--",
                   "TCSlib", "TCSlib.lean", "lean-toolchain", "lake-manifest.json")
    for row in record["source_files"]:
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]

    def check_exchange():
        assert git(publisher, "branch", "--show-current") == record["publisher_branch"]
        assert not git(publisher, "status", "--porcelain"), "The private publisher must be clean."
        assert git(publisher, "remote", "get-url", "--push", "--all", "origin") == REMOTE
        for row in record["files"]:
            assert row["path"].startswith("lwe-sis-constructions/")
            assert hashlib.sha256((publisher / row["path"]).read_bytes()).hexdigest() == row["sha256"]

    check_exchange()
    if args.check_only:
        print("Clean draft and private publisher; frozen sources and all seven payload hashes verified.")
        return
    assert shutil.which("gh"), "GitHub CLI is required."

    def gh(*values):
        return subprocess.check_output(["gh", *values], cwd=ROOT, text=True).strip()

    for number, branch in [(236, "cryptography/lwe-sis-encoding-proofs"),
                           (237, "cryptography/lwe-sis-phase1-statements")]:
        dep = json.loads(gh("pr", "view", str(number), "--repo", REPO, "--json",
                            "headRefName,baseRefName,state"))
        assert dep["headRefName"] == branch
        assert dep["state"] in {"OPEN", "MERGED"} and dep["baseRefName"] == CENTRAL
        if number == 237 and dep["state"] == "OPEN":
            intake = "ff8345b1d2ac2f605d81cdf6c23216aadb918abb"
            assert not git(ROOT, "diff", "--name-only",
                "690217cc1aaefe411158808a8b0797fd887a8abc", intake, "--",
                "TCSlib", "TCSlib.lean", "lean-toolchain", "lake-manifest.json")
            git(ROOT, "push", "--no-follow-tags", "origin", intake + ":refs/heads/" + branch,
                capture=False)
    own_head = git(ROOT, "rev-parse", "HEAD")
    git(ROOT, "push", "--no-follow-tags", "origin", own_head + ":refs/heads/" + TOPIC,
        capture=False)
    prs = json.loads(gh("pr", "list", "--repo", REPO, "--head", TOPIC, "--state", "open",
                       "--json", "number,url,isDraft,baseRefName"))
    assert len(prs) <= 1, "Inspect multiple open PRs before publication."
    title = "State binary representation adapters for cryptographic machines"
    if prs:
        assert prs[0]["isDraft"], "Inspect a PR already marked ready for review."
        gh("pr", "edit", str(prs[0]["number"]), "--repo", REPO, "--base", CENTRAL,
           "--title", title, "--body-file", str(HERE / "PR_BODY.md"))
        pr_url = prs[0]["url"]
    else:
        pr_url = gh("pr", "create", "--repo", REPO, "--head", TOPIC, "--base", CENTRAL,
                    "--draft", "--title", title, "--body-file", str(HERE / "PR_BODY.md"))
    print("Draft PR: " + pr_url, flush=True)
    git(publisher, "-c", "rebase.autoStash=false", "pull", "--rebase", "origin", EXCHANGE,
        capture=False)
    check_exchange()
    pending = git(publisher, "diff", "--name-only", "--no-renames", "FETCH_HEAD", "HEAD").splitlines()
    assert all(p.startswith("lwe-sis-constructions/") for p in pending), pending
    git(publisher, "push", "--no-follow-tags", "origin", "HEAD:refs/heads/" + EXCHANGE,
        capture=False)
    pin = git(publisher, "rev-parse", "HEAD")
    print("\nPublished exchange commit: " + pin)
    print("Selected reviewer: " + args.worker.capitalize())
    print("\nPaste into a fresh " + args.worker.capitalize() + " auditor chat:\n")
    print("Audit the LWE/SIS encoding-adapter statements, round 1, in " + REPO + ".")
    print("Read " + EXCHANGE + " at exact commit " + pin + ".")
    print("Read README.md, lwe-sis-constructions/README.md, then " + record["gate_path"] + "/README.md.")
    print("Verify SHA256SUMS and both revision-qualified BUNDLE-FILES indexes; follow the pack in the first bundle section.")
    print("Frozen Lean/root: " + SOURCE + "; bundled records: " + record["records_pin"] + ".")
    print("Bundle SHA-256: " + record["bundle_sha256"] + "; sections: " + str(record["sections"]) + ".")
    print("Review 20 adapter declarations and 14 admitted obligations, the 263 unchanged earlier constants, and nine consumed machine contracts; central PR target: " + CENTRAL + ".")
    print("Return lwe-sis-adapter-statements-findings.md as Markdown in chat. Do not edit, fill, dispatch workers, push or merge.")
    print("\nNo central/campaign ref was updated; no branch was merged. The user dispatches the review.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit("Publication stopped after exit " + str(error.returncode)
                         + "; inspect the error. No force or merge was attempted.") from None
