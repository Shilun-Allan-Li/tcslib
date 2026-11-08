# Archived host-guard r1 review

Reviewed the exact5,942-byte `b48a00179b04a0bc52a4e04995d50cd0c15505117c2b3dc1928d5da9719b5123` guard preserved in the preparation checkpoint. No proposed program was imported/executed. Two routine fixes are recommended before use; neither expands scope or needs a human mathematical ruling.

* **G-01 — termination cleanup.** `signal` is imported but handlers are not installed. The helper module's handlers live inside its uncalled main. Default SIGTERM/HUP can terminate this wrapper while its separately sessioned child continues. Install handlers that raise `InterruptedError` so the existing protected own-group cleanup runs.
* **G-02 — pins after host waiting.** Recheck tool/helper hashes and live HEAD/clean state after the potentially long idle wait, immediately before Popen. Recheck HEAD/clean after the child too. The existing post-command tool check detects changed tool bytes after they have executed; generic check_probe does not itself verify live HEAD.

The nested final-driver/checker processes retain the guard's child process group, so the foreign-PGID monitor does not mistake them for independent sessions. The cleanup target is the just-created child group, not any host-inventory PID. Expected rc1 remains raw command status and is not called a proof pass. Ordinary PATH/no PFR is preserved.

This review does not test runtime signal delivery, process tables, native marker formatting or final Rule10 coverage. Preserve archived r1; use a separately hashed correction. The preparation checkpoint remains unchanged.
