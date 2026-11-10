"""Publish the verified PR branch and Codex exchange inputs using client credentials.

No campaign ref is a push destination. No merge, force, reset or stash is performed.
The source branch stays at the verified history; only the separate exchange clone rebases.
"""

import hashlib
import json
from pathlib import Path
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REPO = "Shilun-Allan-Li/tcslib"
REMOTE = "https://github.com/" + REPO + ".git"
TOPIC = "cryptography/lwe-sis-encoding-proofs"
TARGET = "cryptography/pass-shelat-ch2-4"
EXCHANGE = "exchange/pass-shelat-ch5-8"
PUBLISHER_BRANCH = "publish/lwe-sis-encoding-proofs-r1"
SOURCE = "893e921bf2afeca293be9da9d495613bb1486796"
PREFIX = "lwe-sis-constructions/"


def git(checkout, *args, capture=True):
    result = subprocess.run(["git", "-C", str(checkout), *args],
                            capture_output=capture, text=True, check=True)
    return result.stdout.strip() if capture else ""


def main():
    record = json.loads((HERE / "review-publication.json").read_text())
    publisher = Path(record["publisher_checkout"])
    assert publisher.name == "tcslib-exchange-lwe-sis-publish"
    assert (publisher / ".git").is_dir()
    assert shutil.which("gh"), "GitHub CLI is needed to create the draft PR."
    assert Path(git(ROOT, "rev-parse", "--show-toplevel")) == ROOT
    assert git(ROOT, "branch", "--show-current") == TOPIC
    assert not git(ROOT, "status", "--porcelain"), "The own PR checkout must be clean."
    assert git(ROOT, "remote", "get-url", "--push", "--all", "origin") == REMOTE
    git(ROOT, "diff", "--exit-code", SOURCE, "HEAD", "--", "TCSlib", "TCSlib.lean",
        "lean-toolchain", "lake-manifest.json")
    for row in record["source_files"]:
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]

    def check_exchange():
        assert git(publisher, "branch", "--show-current") == PUBLISHER_BRANCH
        assert not git(publisher, "status", "--porcelain"), "The publisher must be clean."
        assert git(publisher, "remote", "get-url", "--push", "--all", "origin") == REMOTE
        for row in record["files"]:
            assert row["path"].startswith(PREFIX)
            assert hashlib.sha256((publisher / row["path"]).read_bytes()).hexdigest() == row["sha256"]

    check_exchange()
    own_head = git(ROOT, "rev-parse", "HEAD")
    git(ROOT, "push", "--no-follow-tags", "origin", own_head + ":refs/heads/" + TOPIC,
        capture=False)

    def gh(*args):
        return subprocess.check_output(["gh", *args], cwd=ROOT, text=True).strip()

    prs = json.loads(gh("pr", "list", "--repo", REPO, "--head", TOPIC,
                       "--base", TARGET, "--state", "open", "--json", "number,url,isDraft"))
    assert len(prs) <= 1, "Multiple matching PRs require inspection."
    body = str(HERE / "PR_BODY.md")
    title = "Formalize decisional LWE and SIS foundations"
    if prs:
        pr = prs[0]
        gh("pr", "edit", str(pr["number"]), "--repo", REPO, "--title", title, "--body-file", body)
        if not pr["isDraft"]:
            gh("pr", "ready", str(pr["number"]), "--repo", REPO, "--undo")
        pr_url = pr["url"]
    else:
        pr_url = gh("pr", "create", "--repo", REPO, "--head", TOPIC, "--base", TARGET,
                    "--draft", "--title", title, "--body-file", body)
    print("Draft PR: " + pr_url, flush=True)

    git(publisher, "-c", "rebase.autoStash=false", "pull", "--rebase", "origin", EXCHANGE,
        capture=False)
    check_exchange()
    paths = git(publisher, "diff", "--name-only", "--no-renames", "FETCH_HEAD", "HEAD").splitlines()
    assert all(path.startswith(PREFIX) for path in paths), paths
    git(publisher, "push", "--no-follow-tags", "origin", "HEAD:refs/heads/" + EXCHANGE,
        capture=False)
    pin = git(publisher, "rev-parse", "HEAD")
    gate = record["gate_path"]
    print("\nPublished exchange commit: " + pin)
    print("Gate README: https://github.com/" + REPO + "/blob/" + pin + "/" + gate + "/README.md")
    print("\nPaste into a fresh Codex auditor chat:\n")
    print("Audit the LWE/SIS representation-proof fill, round 1, in " + REPO + ".")
    print("Read " + EXCHANGE + " at exact commit " + pin + ".")
    print("Read README.md, lwe-sis-constructions/README.md, then " + gate + "/README.md.")
    print("Verify SHA256SUMS and the revision-qualified BUNDLE-FILES index; follow the pack in the first bundle section.")
    print("Audited statement freeze: 4364d0e0fe9accd649b6acb4751e8684aa93ad1e; filled source: " + SOURCE + ".")
    print("Records: " + record["records_pin"] + "; bundle SHA-256: " + record["bundle_sha256"] + "; sections: " + str(record["sections"]) + ".")
    print("Review the 14 proofs, interface invariance and evidence. Return lwe-sis-encoding-proofs-findings.md as Markdown in chat.")
    print("Do not edit, fill, dispatch workers, push or merge. Preserve source-archival and scoped-verification limits.")
    print("\nNo campaign ref was updated and no branch was merged.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(f"Publication stopped after command exit {error.returncode}; inspect its error. No force or merge was attempted.") from None
