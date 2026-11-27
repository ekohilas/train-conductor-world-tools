#!/usr/bin/env bash
# Builds a clean branch for one rung of the Fable prompt ladder and writes its prompt.
#
#   scripts/prepare_fable_branch.sh <rung 1-4> [prompt-output-file]
#
# The branch is an orphan commit (no history), so the agent can't find the other rungs,
# the prompts or the review checklist in `git log`. It contains everything in the
# current HEAD except `prompts/` and `scripts/`, plus that rung's frozen
# `lean/TrainNetwork/Goal.lean`. The full prompt (rung header + shared body) is written
# to the output file (default: stdout).
set -euo pipefail

rung="${1:?usage: $0 <rung 1-4> [prompt-output-file]}"
out="${2:-/dev/stdout}"
case "$rung" in 1|2|3|4) ;; *) echo "rung must be 1-4" >&2; exit 1 ;; esac

root="$(git rev-parse --show-toplevel)"
cd "$root"
if [ -n "$(git status --porcelain)" ]; then
  echo "working tree not clean; commit or stash first" >&2
  exit 1
fi

orig="$(git symbolic-ref --short HEAD)"
branch="fable/rung-$rung"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Snapshot the files we need before switching branches.
cp -r prompts "$tmp/prompts"
python3 - "$tmp/prompts/goals" "$rung" "$tmp/Goal.lean" <<'EOF'
import sys
goals, rung, dest = sys.argv[1:]
goal = open(f"{goals}/Rung{rung}.lean").read()
tiny = open(f"{goals}/_tiny.lean").read()
open(dest, "w").write(goal.replace("-- TINY", tiny.rstrip()))
EOF
cat "$tmp/prompts/rung$rung.md" <(echo) "$tmp/prompts/_shared.md" \
  | sed '/^<!--/,/-->$/d' > "$tmp/prompt.md"

git checkout -q --orphan "$branch"
git rm -rq --cached prompts scripts
rm -rf prompts scripts
cp "$tmp/Goal.lean" lean/TrainNetwork/Goal.lean
# Drop README lines that mention the prompt ladder.
python3 - <<'PY'
lines = open("README.md").read().split("\n")
out, skip = [], False
for line in lines:
    if line.startswith("* `prompts/`"):
        skip = True
        continue
    if skip and line.startswith("  "):
        continue
    skip = False
    out.append(line)
open("README.md", "w").write("\n".join(out))
PY
printf 'import TrainNetwork.Problem\nimport TrainNetwork.Cost\nimport TrainNetwork.Goal\n' \
  > lean/TrainNetwork.lean
git add -A
git commit -q -m "Train Network Problem: workspace for a complexity result"
base="$(git rev-parse HEAD)"
git tag -f "fable-rung-$rung-base" "$base" >/dev/null

# Return to where we started.
git checkout -q -f "$orig"

cp "$tmp/prompt.md" "$out" 2>/dev/null || cat "$tmp/prompt.md"
echo "branch $branch at $base (tag fable-rung-$rung-base); prompt -> $out" >&2
