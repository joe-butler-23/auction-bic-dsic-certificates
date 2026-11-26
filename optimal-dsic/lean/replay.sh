#!/usr/bin/env bash
# Rebuild the proof from source and regenerate logs/ (deterministic output, no timings).
# Requires elan (lean4 v4.36.0 is selected by lean-toolchain).
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p logs
lake exe cache get >/dev/null
lake build >/dev/null
# 1. Source manifest + statement check + axiom footprint of every top-level theorem.
{
  LC_ALL=C sha256sum EconCSAuction.lean EconCSAuction/*.lean CleanRoomAudit.lean
  echo "---"
  lake env lean CleanRoomAudit.lean
} > logs/cleanroom_audit.log
# 2. Independent kernel replay of every module that contains declarations.
: > logs/leanchecker.log
for m in Spec MeasureHelpers SubgradIBP Lemma1 Lemma2 Lemma3 Lemma4 Lemma5 Lemma5Sharp \
         Theorem1 Theorem2 Proof; do
  if lake env leanchecker "EconCSAuction.$m" >/dev/null 2>&1; then
    echo "PASS EconCSAuction.$m" >> logs/leanchecker.log
  else
    echo "FAIL EconCSAuction.$m" >> logs/leanchecker.log
  fi
done
if lake env leanchecker CleanRoomAudit >/dev/null 2>&1; then
  echo "PASS CleanRoomAudit" >> logs/leanchecker.log
else
  echo "FAIL CleanRoomAudit" >> logs/leanchecker.log
fi
cat logs/leanchecker.log
! grep -q FAIL logs/leanchecker.log
