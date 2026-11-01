#!/usr/bin/env bash
# Create a git worktree for an implementation task, sharing the prebuilt Mathlib packages.
# Usage: scripts/new_worktree.sh <name>     (creates ../wt-rmi/<name> on branch impl/<name>)
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"
wt="$(dirname "$root")/wt-rmi/$name"
git -C "$root" worktree add -q -b "impl/$name" "$wt" HEAD
mkdir -p "$wt/.lake"
ln -s "$root/.lake/packages" "$wt/.lake/packages"
echo "$wt"
