# C3 module-list hash provenance

The frozen C3 manifest key `module_list_sha256` is imprecisely named. Its value `e027117c0810eabb2cf743e19517ab36ce57ca171a700a510547aaeb966d8d35` hashes `final-explicit-files.txt`: exactly 54 repository-relative Lean source paths, each followed by one newline. It was carried from the explicit catalog manifest's `files_sha256` field. It does not hash `modules.json` or a dotted-module-name serialization.

Replacing each source path's final `.lean` and `/` separators yields exactly the frozen C3 manifest's 54-module array, in the same order. That array and source imports match Gate06 final `modules.json`. The bounded C3 extractor will bind both the exact file-list bytes and the fresh modules JSON. No frozen artifact or source/HEAD was changed to clarify this provenance.
