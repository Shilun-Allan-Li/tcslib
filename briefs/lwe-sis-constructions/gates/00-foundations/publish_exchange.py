"""Publish only the prepared LWE/SIS namespace from its dedicated exchange clone.

The user runs this when sandbox networking is unavailable. It rebases immediately
before a normal fast-forward push, without touching the shared exchange checkout.
"""

import hashlib
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
RECEIPT = HERE / "exchange-publication.json"
REMOTE = "https://github.com/Shilun-Allan-Li/tcslib.git"
DESTINATION = "refs/heads/exchange/pass-shelat-ch5-8"
EXPECTED_BRANCH = "publish/lwe-sis-phase0-r1"
NAMESPACE = "lwe-sis-constructions/"


def main():
    record = json.loads(RECEIPT.read_text())
    checkout = Path(record["publisher_checkout"])
    assert checkout.name == "tcslib-exchange-lwe-sis-publish"
    assert (checkout / ".git").is_dir(), "Expected the dedicated independent clone."

    def git(*args, capture=True):
        result = subprocess.run(["git", "-C", str(checkout), *args],
                                capture_output=capture, text=True, check=True)
        return result.stdout.strip() if capture else ""

    def verify_payload():
        for row in record["files"]:
            assert row["path"].startswith(NAMESPACE)
            data = (checkout / row["path"]).read_bytes()
            assert hashlib.sha256(data).hexdigest() == row["sha256"], row["path"]
        assert not git("status", "--porcelain"), "Dedicated publisher must be clean."
        assert git("branch", "--show-current") == EXPECTED_BRANCH
        assert git("remote", "get-url", "--push", "--all", "origin") == REMOTE

    assert Path(git("rev-parse", "--show-toplevel")) == checkout.resolve()
    verify_payload()
    git("-c", "rebase.autoStash=false", "pull", "--rebase", "origin",
        "exchange/pass-shelat-ch5-8", capture=False)
    verify_payload()
    pending = git("diff", "--name-only", "--no-renames", "FETCH_HEAD", "HEAD").splitlines()
    assert all(path.startswith(NAMESPACE) for path in pending), pending
    git("push", "--no-follow-tags", "origin", "HEAD:" + DESTINATION, capture=False)
    pin = git("rev-parse", "HEAD")
    gate = "lwe-sis-constructions/outbox/gates/00-foundations-r1"
    print("\nPublished exchange commit: " + pin)
    print("Gate README: https://github.com/Shilun-Allan-Li/tcslib/blob/" + pin + "/" + gate + "/README.md")
    print("\nPaste into a fresh Codex auditor chat:\n")
    print("Audit phase 0 round 1 of the separate LWE/SIS construction campaign in Shilun-Allan-Li/tcslib.")
    print("Read exchange/pass-shelat-ch5-8 at exact commit " + pin + ".")
    print("Read README.md, lwe-sis-constructions/README.md, then " + gate + "/README.md.")
    print("Verify SHA256SUMS and the revision-qualified BUNDLE-FILES index. Follow the frozen pack in the bundle's first section.")
    print("Frozen Lean/root: 4364d0e0fe9accd649b6acb4751e8684aa93ad1e; bundled records: 06cdbc030168d9e6662b12960882d8ca6f5b1fa7.")
    print("Bundle SHA-256: 9e39453ac97f8fbdc8014a302aa18c40b41f7e4692641ca5b141e0d79f25e68b; 155 sections.")
    print("Audit statements, sketches and readers only; do not fill proofs, dispatch workers, push or merge.")
    print("Return lwe-sis-phase0-findings.md as a Markdown file in chat, including severity counts and source-fidelity limits.")
    print("\nNo campaign branch was a push destination. No branch was merged.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(
            f"Publication stopped after Git exited {error.returncode}; "
            "inspect the error above. No forced update was attempted.") from None
