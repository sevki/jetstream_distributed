#!/usr/bin/env bash
# Publish the built book to the `gh-pages` branch.
#
#   publish-book.sh main        the book for the default branch, at the root
#   publish-book.sh pr N        a preview of pull request N, at pr-preview/pr-N/
#   publish-book.sh remove N    delete that preview (the PR closed)
#
# Everything lives on one branch so that GitHub Pages ("deploy from a branch",
# `gh-pages`, `/`) serves it without a third-party action holding a write token:
#
#   /                     the book as of main
#   /pr-preview/pr-N/     the book as of pull request N
#
# `main` replaces everything at the root *except* `pr-preview/`, and a preview
# touches only its own directory, so neither can wipe the other out.
#
# Environment:
#   BOOK_DIR   the built book (default: book/build); not needed for `remove`
#   REMOTE     the git remote to publish to (default: origin)
#   BRANCH     the branch to publish on (default: gh-pages)
#   MESSAGE    the commit message (default: derived from the mode)
set -euo pipefail

mode="${1:?usage: publish-book.sh main | pr N | remove N}"
pr="${2:-}"
book="${BOOK_DIR:-book/build}"
remote="${REMOTE:-origin}"
branch="${BRANCH:-gh-pages}"

case "$mode" in
  main) ;;
  pr | remove)
    [[ "$pr" =~ ^[0-9]+$ ]] || { echo "pr number required, got '$pr'" >&2; exit 2; }
    ;;
  *) echo "unknown mode '$mode'" >&2; exit 2 ;;
esac
if [[ "$mode" != remove && ! -f "$book/index.html" ]]; then
  echo "no built book at $book (no index.html)" >&2
  exit 2
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# `actions/checkout` authenticates through an `http.*.extraheader` in this
# repository's config, which a fresh clone does not inherit. Every git command
# below that talks to the remote is given it, so the clone *and* the push are
# authorised without a token ever appearing in a command line.
#
# The clone needs it as much as the push does: an earlier version copied the
# header only after cloning, and so worked the first time (there was no branch to
# clone) and failed every time after, on a repository that needs credentials.
#
# The two commands that read the remote run from `$work`, not from the checkout.
# The checkout already has the header in its own config, and `-c` adds to what is
# there instead of replacing it: run from the checkout, the header went out twice
# and GitHub answered `400 Duplicate header: "Authorization"`.
auth=()
while IFS= read -r entry; do
  [[ -n "$entry" ]] || continue
  auth+=(-c "${entry%% *}=${entry#* }")
done < <(git config --local --get-regexp '^http\..*extraheader$' || true)

url="$(git remote get-url "$remote")"
# `-C` changes what a relative path means, so a remote that is a local path is made absolute.
[[ -e "$url" ]] && url="$(cd "$url" && pwd)"

# A clone of the branch, or an empty history to start it from. `--exit-code`
# makes `ls-remote` return 2 for "no such branch" and something else for a real
# failure, and only the first means there is nothing to clone: treating every
# failure as "no branch" would start a fresh history over an authentication error.
set +e
git -C "$work" "${auth[@]}" ls-remote --exit-code --heads "$url" "$branch" >/dev/null
found=$?
set -e
case "$found" in
  0)
    git -C "$work" "${auth[@]}" clone --quiet --branch "$branch" --single-branch "$url" site
    ;;
  2)
    git init --quiet "$work/site"
    git -C "$work/site" checkout --quiet --orphan "$branch"
    git -C "$work/site" remote add "$remote" "$url"
    ;;
  *)
    echo "could not read $remote (git ls-remote exited $found)" >&2
    exit 1
    ;;
esac
site="$work/site"
# A clone made with `-c` keeps those settings, but a fresh `git init` does not,
# and the push needs them either way.
for ((i = 0; i < ${#auth[@]}; i += 2)); do
  git -C "$site" config --replace-all "${auth[i + 1]%%=*}" "${auth[i + 1]#*=}"
done
git -C "$site" config user.name "${GIT_AUTHOR_NAME:-github-actions[bot]}"
git -C "$site" config user.email "${GIT_AUTHOR_EMAIL:-41898282+github-actions[bot]@users.noreply.github.com}"

abs_book=""
[[ "$mode" != remove ]] && abs_book="$(cd "$book" && pwd)"

apply() {
  case "$mode" in
    main)
      # Everything but the previews and git's own directory.
      find "$site" -mindepth 1 -maxdepth 1 ! -name .git ! -name pr-preview -exec rm -rf {} +
      cp -a "$abs_book"/. "$site"/
      ;;
    pr)
      rm -rf "$site/pr-preview/pr-$pr"
      mkdir -p "$site/pr-preview/pr-$pr"
      cp -a "$abs_book"/. "$site/pr-preview/pr-$pr"/
      ;;
    remove)
      rm -rf "$site/pr-preview/pr-$pr"
      ;;
  esac
  # Pages would otherwise run the site through Jekyll, which drops files and
  # directories that start with an underscore.
  touch "$site/.nojekyll"
}

default_message() {
  case "$mode" in
    main) echo "book: main at ${GITHUB_SHA:-unknown}" ;;
    pr) echo "book: preview of #$pr at ${GITHUB_SHA:-unknown}" ;;
    remove) echo "book: remove the preview of #$pr" ;;
  esac
}
message="${MESSAGE:-$(default_message)}"

# Another job may push between our clone and our push (a preview and main run
# side by side), so a rejected push re-reads the branch and applies again. The
# wait is random: a fixed one makes publishers that collided collide again.
attempts=10
for attempt in $(seq 1 "$attempts"); do
  apply
  git -C "$site" add -A
  if git -C "$site" diff --cached --quiet; then
    echo "nothing to publish: $branch already has this"
    exit 0
  fi
  git -C "$site" commit --quiet -m "$message"
  if git -C "$site" push --quiet "$remote" "HEAD:refs/heads/$branch"; then
    echo "published ($mode${pr:+ $pr}) on attempt $attempt"
    exit 0
  fi
  echo "push rejected on attempt $attempt; re-reading $branch" >&2
  git -C "$site" fetch --quiet "$remote" "$branch"
  git -C "$site" reset --quiet --hard "FETCH_HEAD"
  sleep $((RANDOM % (attempt + 2) + 1))
done
echo "could not publish after $attempts attempts" >&2
exit 1
