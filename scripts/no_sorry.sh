#!/usr/bin/env bash
# Sorry-gate: fail if any `sorry` / `admit` / `native_decide` / `axiom`
# declaration appears in the committed Lean sources. Run locally and in CI.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0

if grep -RnE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)' \
    DlnDynamics --include='*.lean'; then
  echo "ERROR: forbidden token (sorry/admit/native_decide) in DlnDynamics/." >&2
  status=1
fi

if grep -RnE '^[[:space:]]*axiom[[:space:]]' DlnDynamics --include='*.lean'; then
  echo "ERROR: 'axiom' declaration in DlnDynamics/." >&2
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "sorry-gate: OK (no sorry/admit/native_decide/axiom in DlnDynamics/)."
fi
exit "$status"
