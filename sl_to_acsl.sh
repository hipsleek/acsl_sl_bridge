#!/usr/bin/env sh
set -eu

USE_GUI=0

# Parse flags
if [ "${1:-}" = "--gui" ]; then
  USE_GUI=1
  shift
fi

# Input handling
if [ "$#" -eq 1 ]; then
  INPUT="$1"
else
  INPUT="$(mktemp --suffix=.c)"
  cat > "$INPUT"
fi

# Run SL -> ACSL translator
dune exec ./src/main.exe -- "$INPUT"

DIR="$(dirname "$INPUT")"
BASE="$(basename "$INPUT")"     # e.g. foo.c
STEM="${BASE%.*}"               # e.g. foo

ACSL_FILE="$DIR/${STEM}_acsl.c"

if [ ! -f "$ACSL_FILE" ]; then
  echo "Error: ACSL output not found: $ACSL_FILE" >&2
  exit 1
fi

# Run Frama-C
if [ "$USE_GUI" -eq 1 ]; then
  frama-c-gui -wp -wp-no-simpl -wp-no-let "$ACSL_FILE"
else
  frama-c -wp -wp-no-simpl -wp-no-let "$ACSL_FILE"
fi
