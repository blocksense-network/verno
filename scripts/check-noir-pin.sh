#!/usr/bin/env bash
# Guard the Noir pin.
#
# Verno spent thirteen Noir releases drifting because nothing could report how old its pin
# was: the repository had no CI at all, and the pin was a *branch* on a fork
# (`blocksense-network/noir` `patched-master`), so `Cargo.lock` churn was indistinguishable
# from somebody moving the fork.
#
# This script enforces the three properties that make the pin legible, and it is cheap
# enough (no build) to be the first thing CI runs:
#
#   1. every Noir dependency comes from `noir-lang/noir`, not a fork;
#   2. there is no `[patch]` section redirecting them anywhere else;
#   3. all of them are pinned to the *same* immutable tag.
#
# Optionally (--check-drift), it also reports how many releases behind upstream's latest
# the pin is, and fails past MAX_RELEASES_BEHIND.
#
# Usage:
#   scripts/check-noir-pin.sh                # properties 1-3, offline
#   scripts/check-noir-pin.sh --check-drift  # also contact GitHub for the latest release

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$REPO_ROOT/Cargo.toml"
LOCKFILE="$REPO_ROOT/Cargo.lock"

# How far behind upstream's newest release the pin may be before CI fails. Upstream cuts a
# beta roughly every three weeks, so two releases is about six weeks — still a diff a person
# can read in one sitting, which is the whole point of catching drift early.
MAX_RELEASES_BEHIND=2

fail() { echo "check-noir-pin: $*" >&2; exit 1; }

# --- 1. no fork, no [patch] --------------------------------------------------------

if grep -q '^\[patch\.' "$MANIFEST"; then
    fail "Cargo.toml has a [patch] section.
  Verno depended on a Noir fork for the seven Blocksense patches it needed. All seven were
  upstreamed (noir-lang/noir#9981 in v1.0.0-beta.14 and #9979 in v1.0.0-beta.16), so the
  fork was retired and the [patch] block deleted. Reintroducing one hides the real pin."
fi

if grep -q 'blocksense-network/noir' "$MANIFEST"; then
    fail "Cargo.toml still references blocksense-network/noir. That fork is retired; see above."
fi

# --- 2. one tag, and only tags -----------------------------------------------------

# Every `git = ".../noir.git"` dependency line, with its tag (if any).
# Read with a plain while-loop rather than `mapfile`, which macOS' bash 3.2 does not have.
noir_lines=""
while IFS= read -r line; do
    noir_lines="${noir_lines}${line}"$'\n'
done < <(grep -n 'github\.com/noir-lang/noir\.git' "$MANIFEST" || true)

if [ -z "$noir_lines" ]; then
    fail "no noir-lang/noir dependencies found in Cargo.toml — did the manifest move?"
fi

tags=()
while IFS= read -r line; do
    [ -n "$line" ] || continue
    if [[ "$line" =~ branch[[:space:]]*=[[:space:]]*\"([^\"]+)\" ]]; then
        fail "a Noir dependency is pinned to branch \"${BASH_REMATCH[1]}\":
  ${line}
  Pin a release tag instead. A branch pin makes drift invisible: the revision moves
  underneath you and Cargo.lock churn stops meaning anything."
    fi
    if [[ "$line" =~ rev[[:space:]]*=[[:space:]]*\"([^\"]+)\" ]]; then
        fail "a Noir dependency is pinned to a bare revision \"${BASH_REMATCH[1]}\":
  ${line}
  Pin a release tag instead, so the distance to upstream is readable."
    fi
    if [[ "$line" =~ tag[[:space:]]*=[[:space:]]*\"([^\"]+)\" ]]; then
        tags+=("${BASH_REMATCH[1]}")
    else
        fail "a Noir dependency has no tag:
  ${line}"
    fi
done <<< "$noir_lines"

unique_tags=$(printf '%s\n' "${tags[@]}" | sort -u)
if [ "$(printf '%s\n' "$unique_tags" | wc -l)" -ne 1 ]; then
    fail "Noir dependencies disagree on the pinned tag:
$(printf '  %s\n' $unique_tags)"
fi

PIN="$unique_tags"
echo "check-noir-pin: pinned to noir-lang/noir $PIN (${#tags[@]} dependencies, all agreeing)"

# --- 3. the lockfile agrees --------------------------------------------------------
#
# This is what makes an unaccompanied pin bump fail fast. Changing the tag in Cargo.toml
# without regenerating Cargo.lock leaves the two disagreeing; `cargo --locked` would also
# catch it, but only after a full dependency resolve, and the error it prints does not say
# what actually happened.

if [ -f "$LOCKFILE" ]; then
    if ! grep -q "noir.git?tag=$PIN" "$LOCKFILE"; then
        locked=$(grep -o 'noir\.git?tag=[^#"]*' "$LOCKFILE" | sort -u | head -3 || true)
        fail "Cargo.toml pins $PIN but Cargo.lock records:
$(printf '  %s\n' ${locked:-<nothing>})
  Bumping the Noir pin is not a one-line change: regenerate the lockfile and do the
  porting work the new release needs."
    fi
    echo "check-noir-pin: Cargo.lock agrees"
fi

# --- 4. drift against upstream's latest release ------------------------------------

if [ "${1:-}" != "--check-drift" ]; then
    exit 0
fi

echo "check-noir-pin: asking GitHub for noir-lang/noir's releases..."
# Release tags only; `nightly-*` tags are not releases and must not count as drift.
releases=$(git ls-remote --tags https://github.com/noir-lang/noir 'v1.0.0-beta.*' \
    | sed 's|.*refs/tags/||' | grep -v '\^{}' | sort -V)

latest=$(printf '%s\n' "$releases" | tail -1)
behind=$(printf '%s\n' "$releases" | sed -n "/^$(printf '%s' "$PIN" | sed 's/\./\\./g')\$/,\$p" | tail -n +2 | wc -l | tr -d ' ')

echo "check-noir-pin: pinned $PIN, upstream latest $latest, $behind release(s) behind"

if [ "$behind" -gt "$MAX_RELEASES_BEHIND" ]; then
    fail "the Noir pin is $behind releases behind $latest (limit $MAX_RELEASES_BEHIND).
  Bump it now, while the diff is still readable. Verno reached thirteen releases behind
  because nothing reported this number."
fi
