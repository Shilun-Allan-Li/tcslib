The issued addendum requires one Lean process per host. A later host audit observed other workers and the Lamport Statistics check was interrupted to restore compliance.

User override in this Codex chat: “Override; up to three Lean processes on this Mac are allowed at a time. Until a slot is available, wait or do source-only work.”

Subsequent Lamport checks are gated by evidence/tools/lean_host_guard.py. Our worker still checks one module at a time. No external worker process is terminated.

The first combined ps(pid,comm,args) count was unreliable because macOS truncates comm in that layout. The guard uses ps(pid,comm) alone, verified against the observed executable paths.

Later Seyoon-authorized coordination note from dl-crh chat: leave one of the shared three slots for dl-crh bootstrap, across all projects on this host. Lamport conservatively starts a check only with fewer than two existing Lean processes, retaining one free slot after its own start. The total cap remains three while running.

Read-only verification at 2026-11-14T08:03:54.061699+00:00 confirmed dl-crh completed its98-module exactbase bootstrap with all exit0 and is now in its final sweep. The coordination note was specifically for its bootstrap. The temporary extra reservation is therefore released; new guard invocations start with fewer than3 existing Lean processes, retaining the shared cap3 and one Lamport module at a time. Observation and hashes: logs/dl-crh-bootstrap-reservation-release.json. No outbound chat message was sent.

At 2026-11-14T08:22:39.528Z, after further shared-cap interruptions, the user explicitly authorized “Send the coordination note”. The concrete approved note was sent once to the four active peer worker chats. Exact text, recipients and successful tool receipts are preserved in requests/worker-coordination-note-authorized.json. No peer process was changed.
