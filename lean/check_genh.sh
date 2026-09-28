#!/usr/bin/env bash
# Check the general-Hamiltonian extension: `STUProof/GeneralH.lean` (the STU conjecture for an
# arbitrary Hermitian H) and `STUProof/AxiomsGenH.lean` (its axiom check). Run from the project root
# (this `lean/` directory, after `lake exe cache get`) with the Lean toolchain on PATH, after `check.sh`:
#   export PATH="$HOME/.elan/bin:$PATH"; bash check.sh && bash check_genh.sh
# If the .olean of `STUProof.KirwanFreeFinal` is missing, or with `--full`, this script first runs
# `check.sh` itself.
# Before each Lean process it waits (polling every 45 s) until no other `lean` process is running
# and at least $MIN_FREE_MB (default 6000) MB of RAM are available.
set -euo pipefail
out=.lake/build/lib/lean/STUProof
min_mb=${MIN_FREE_MB:-6000}
mkdir -p "$out"

# Prints "<number of running lean processes> <available RAM in MB>".
ram_state() {
  if command -v powershell.exe >/dev/null 2>&1; then
    powershell.exe -NoProfile -NonInteractive -Command \
      '$n = @(Get-Process lean -ErrorAction SilentlyContinue).Count; $a = [int](Get-Counter "\Memory\Available MBytes").CounterSamples.CookedValue; Write-Output "$n $a"' \
      | tr -d '\r'
  else
    local n a
    n=$( (pgrep -x lean || true) | wc -l)
    a=$(awk '/MemAvailable/ {print int($2 / 1024)}' /proc/meminfo)
    echo "$n $a"
  fi
}

wait_for_ram() {
  local n a
  while true; do
    read -r n a < <(ram_state)
    if [ "$n" -eq 0 ] && [ "$a" -ge "$min_mb" ]; then
      return 0
    fi
    echo "   waiting: $n lean process(es) running, $a MB available (need 0 and >= $min_mb MB)"
    sleep 45
  done
}

if [ "${1:-}" = "--full" ] || [ ! -f "$out/KirwanFreeFinal.olean" ]; then
  wait_for_ram
  bash check.sh
fi

echo "== STUProof/GeneralH.lean"
wait_for_ram
lake env lean -o "$out/GeneralH.olean" -i "$out/GeneralH.ilean" STUProof/GeneralH.lean
echo "== STUProof/AxiomsGenH.lean"
wait_for_ram
lake env lean STUProof/AxiomsGenH.lean
echo "== forbidden keywords (sorry/admit/axiom/native_decide) in GeneralH.lean, AxiomsGenH.lean:"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' STUProof/GeneralH.lean STUProof/AxiomsGenH.lean \
  || echo "none"
