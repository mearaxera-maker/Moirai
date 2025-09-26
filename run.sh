#!/bin/bash
# run.sh - runs TLC on several configs (assumes tla2tools/tlc is on PATH or using TLA+ Toolbox)
# Edit TLC command to match your local setup. Example:
# java -cp path/to/tla2tools.jar tlc2.TLC GMU_Patched_Run.tla -config gmu_safe.cfg

MODULE="GMU_Patched_Run.tla"

echo "Run: safe config"
java -cp tla2tools.jar tlc2.TLC "${MODULE}" -config gmu_safe.cfg

echo "Run: paradox no guard"
java -cp tla2tools.jar tlc2.TLC "${MODULE}" -config paradox_no_guard.cfg

echo "Run: paradox with guard"
java -cp tla2tools.jar tlc2.TLC "${MODULE}" -config paradox_with_guard.cfg
