#!/bin/bash

set -e
set -o pipefail

# The dune project root is the repository root, one level above this script.
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="$ROOT/_build/default"

# Define logical paths, one per dune theory root. Nested theories
# (osiris.lang, osiris.stdlib.proofs, ...) live in subdirectories whose
# names match their logical names, so they are covered by their parent.
LOGICAL_PATHS=(
  "$BUILD/rocq-osiris/theories=osiris"
  "$BUILD/rocq-osiris/utils=osiris.utils"
  "$BUILD/rocq-osiris/lib=osiris.lib"
  "$BUILD/rocq-osiris/stdlib=osiris.stdlib"
  "$BUILD/examples=osiris.examples"
)

# Collect module names for each path
MODULES=()

for entry in "${LOGICAL_PATHS[@]}"; do
  PHYS_DIR="${entry%%=*}"
  LOGICAL_NS="${entry##*=}"

  if [ ! -d "$PHYS_DIR" ]; then
    echo "check-axioms: $PHYS_DIR does not exist; run make first." >&2
    exit 1
  fi

  MODS=$(find "$PHYS_DIR" -name "*.vo" | sed -e "s|$PHYS_DIR/||" -e 's|\.vo$||' -e 's|/|.|g' | sed "s|^|$LOGICAL_NS.|")
  MODULES+=($MODS)
done

if [ ${#MODULES[@]} -eq 0 ]; then
  echo "check-axioms: no compiled modules found; run make first." >&2
  exit 1
fi

# Build -R flags
R_FLAGS=()
for entry in "${LOGICAL_PATHS[@]}"; do
  PHYS_DIR="${entry%%=*}"
  LOGICAL_NS="${entry##*=}"
  R_FLAGS+=("-R" "$PHYS_DIR" "$LOGICAL_NS")
done

echo "Running rocqchk on ${#MODULES[@]} modules, this may take a minute or two..."
rocqchk -silent -o "${R_FLAGS[@]}" "${MODULES[@]}" 2>&1 | grep -v -E "Corelib\.Floats|Corelib\.Numbers|Stdlib\.Reals"
