#!/usr/bin/env bash
# proto/scripts/run.sh - run TLC on canonical configs (paths are repo-relative)
# Usage (from repo root): proto/scripts/run.sh patched
set -euo pipefail

TLA_TOOL_JAR="${TLA_TOOL_JAR:-tla2tools.jar}"  # set env var TLA_TOOL_JAR if needed

case "${1:-patched}" in
  patched)
    MODULE="../GMU_Patched_Run.tla"
    CONFIG="../configs/gmu_safe.cfg"
    echo "Running patched (runnable) model: ${MODULE} with ${CONFIG}"
    java -cp "${TLA_TOOL_JAR}" tlc2.TLC "${MODULE}" -config "${CONFIG}"
    ;;
  patched-paradox-no-guard)
    MODULE="../GMU_Patched_Run.tla"
    CONFIG="../configs/paradox_no_guard.cfg"
    java -cp "${TLA_TOOL_JAR}" tlc2.TLC "${MODULE}" -config "${CONFIG}"
    ;;
  patched-paradox-guard)
    MODULE="../GMU_Patched_Run.tla"
    CONFIG="../configs/paradox_with_guard.cfg"
    java -cp "${TLA_TOOL_JAR}" tlc2.TLC "${MODULE}" -config "${CONFIG}"
    ;;
  ultimate)
    MODULE="../GMU_Ultimate_Enhanced_Full.tla"
    CONFIG="../configs/GMU_Ultimate_Enhanced_Full.cfg"
    echo "Running ultimate (research) model: ${MODULE} with ${CONFIG}"
    echo "Warning: reduce constants in the .cfg for tractable TLC runs."
    java -cp "${TLA_TOOL_JAR}" tlc2.TLC "${MODULE}" -config "${CONFIG}"
    ;;
  *)
    echo "Usage: $0 {patched|patched-paradox-no-guard|patched-paradox-guard|ultimate}"
    exit 2
    ;;
esac
