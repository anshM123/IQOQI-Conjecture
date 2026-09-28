#!/usr/bin/env bash
# Check every STUProof file in dependency order (sequentially, to bound memory: peak ~6.5 GB).
# Run from this directory (the Lake project root) after `lake exe cache get`, e.g.
#   export PATH="$HOME/.elan/bin:$PATH"; lake exe cache get; bash check.sh
# Each file is elaborated by `lake env lean`; its .olean is written to the project's
# (git-ignored) build directory so that the next file can import it.
set -euo pipefail
out=.lake/build/lib/lean/STUProof
mkdir -p "$out"
for f in SchurHorn Construction Lemma5 STU \
         KirwanFreeCore KirwanFreeHook HookCertificates KirwanFree \
         HookDoubling HookCertSplit \
         HookCert21 HookCert23 HookCert25 HookCert27 HookCert29 \
         HookCert31 HookCert33 HookCert35 HookCert37 HookCert39 \
         KirwanFree40 \
         IntervalUnif KirwanFreeU Renewal CrossUnif KirwanFreeAllD ShortNonnegSmall; do
  echo "== STUProof/$f.lean"
  lake env lean -o "$out/$f.olean" -i "$out/$f.ilean" "STUProof/$f.lean"
done
echo "== STUProof/Axioms.lean"
lake env lean STUProof/Axioms.lean
echo "== forbidden keywords (sorry/admit/axiom/native_decide):"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' STUProof/*.lean || echo "none"
