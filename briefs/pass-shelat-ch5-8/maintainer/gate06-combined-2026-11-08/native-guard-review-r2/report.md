# Host-guard R2 bounded re-review

Read all152 lines /8,104 bytes of `guard_native_command_r2.py`, SHA256 `a1138227d39f2068bdfc75923e80537c577c50c445f998c050189c46f6900ed3`. **Both R1 findings are resolved; no new blocker, major or minor was found in this bounded static review.**

G-01: SIGTERM/HUP handlers now raise through the protected lease/child lifecycle. The invocation records lease acquisition before removing only its own lease, has own-child cleanup in both failure paths, and restores prior signal handlers. Imported `stop_own_group(None, proc)` is valid for the pinned helper: the method reads no self fields and only signals the just-created child group.

G-02: `quick_pins` repeats after idle waiting, immediately before Popen, and after the child. It checks tool/helper/self bytes, actual HEAD/clean state, all1109 source paths/hashes, pinned source inventory, and the same successful bootstrap receipt. The current inventory and all1109 source bytes match; all three helper/tool hashes match. The guard requires a completed same-source successful bootstrap before lease acquisition or native launch.

The nested final-driver/checker subprocesses preserve the guard child PGID. Ordinary PATH/no PFR, real Lean binary pin, fresh output label, raw expected rc1 and `outcome_interpreted:false` remain intact. This wrapper makes no proof/coverage acceptance decision; underlying driver/object/Name/marker validation is still required.

R1 source SHA `b48a00179b04a0bc52a4e04995d50cd0c15505117c2b3dc1928d5da9719b5123`, its two review files, and the archived checkpoint remain unchanged. The R1-to-R2 diff is retained here as data.

No guard/helper import or execution, signal/process simulation, native/cache/app operation, or source/Git/MAIN/exchange mutation was performed. Runtime behavior and gate acceptance remain untested. Root may use only reviewed R2 after bootstrap succeeds; no new user ruling is needed.
