#!/usr/bin/env bash
# dc.sh <file.lean>: devcheck on wt-fill-bb1-machine with dl-oleans (no -o).
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
timeout 1800 bash $SP/dl-review/fill-bb1-machine/tools-used/devcheck.sh $SP/wt-fill-bb1-machine $SP/dl-oleans "$1" 2>&1
