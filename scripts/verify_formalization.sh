#!/usr/bin/env bash

set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_dir"

echo "Checking for unfinished proof declarations and custom axioms..."
if rg -n --glob '*.lean' \
    '^[[:space:]]*(sorry|admit|axiom)[[:space:]]|:=[[:space:]]*(sorry|admit)([[:space:]]|$)' \
    NormFormula NormFormula.lean; then
  echo "Found an unfinished proof declaration or custom axiom." >&2
  exit 1
fi

echo "Building the full project..."
lake build

echo "Auditing kernel dependencies of the public paper claims..."
lake env lean scripts/PaperClaimAxiomAudit.lean

echo "Auditing elementary and whole-paper proof dependencies..."
lake env lean scripts/ElementaryProofAudit.lean

echo "Lean source totals:"
find NormFormula -name '*.lean' -print0 | xargs -0 wc -l | tail -1

echo "Formalization verification passed."
