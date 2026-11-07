# Gate 08 round 2 — Codex follow-up for #227

**Ready for user dispatch; not dispatched by the maintainer.** Gate 08 remains on HOLD and
#227 is not clear to merge until the external follow-up closes at zero blockers and zero majors.

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Lean head: `84f35910912bd3d1cd520beea9469e0ed45ce504` (`cryptography/pass-shelat-ch2-4-shared-s1`).
- Checked base: `bee51909a5c581bd61e954d6e1d86c708b4bc804` (includes the user's #195 merge).
- Records snapshot: `11daf06237ab298fbe8dfdc27b382bd7bd741c08` (`cryptography/pass-shelat-ch2-4`).
- Bundle: `gate08-shared-r2-bundle.md`, SHA-256 `2e6b018933b65074cb41ca48d1986293b3b9cebffe5c766dfbaf8df4bed8b33e`.
- Manifest: `BUNDLE-FILES.txt`, 153 revision-qualified sections, each verified against `git show`.

**Selected worker: Codex (user).** Return **`gate08-shared-r2-findings.md` as a Markdown file
in the audit chat**; use a ZIP only for additional evidence if needed. Do not push to GitHub
or edit a campaign branch. This delivery route supersedes the frozen round-1 push instructions.

Read this README and verify `SHA256SUMS`; begin with the bundle's `pack-r2.md`, verbatim findings,
resolutions and `evidence-r2/REPORT.md` sections. The remaining sections provide the pinned
source, registry, checks and limits. All 153 sections are independently reconstructible from
the manifest. Read the complete root registry to verify H15, rather than relying on an excerpt.

The follow-up checks G08-01–04 and G08-N1/N2, the repair merge, and the stronger evidence.
The cold replay passed 437/437 with zero errors. Expanded and conservative seals have zero
touched failures; inherited failures, non-rerun base controls, and invalid harness attempts are
qualified in the report. Audit the classifications independently. The host proof remains an
authorized `sorry` for the later external S2 fill: this is not a proof fill or its dispatch.

The source book is `Pass–Shelat.pdf` on the campaign branch, SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`;
book page = PDF page − 12. If running Lean, use the pinned toolchain, narrowed roots and
`scripts/lean_check_tree.sh`; never a library-wide build or unfiltered cache get.

This is a Pass–shelat folder on a shared orphan exchange branch. Do not alter any other
campaign's files or staging. The user dispatches the audit and merges PRs.
