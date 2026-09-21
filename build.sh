#!/usr/bin/env bash
# Build the paper with pdflatex + bibtex.
#
# JMLR production compiles with latexmk via pdflatex, so pdflatex is the
# toolchain that matters (not XeTeX/tectonic).
#
#   ./build.sh            # build main.tex   (modular source, out: build-main/)
#   ./build.sh paper      # build paper.tex  (single file,    out: build-paper/)
#   ./build.sh --help
#
# Run `python3 flatten.py` first if you edited sections/*.tex and want the
# single-file version refreshed.
#
# Portability: no hard-coded TeX path. The script uses $PDFLATEX / $BIBTEX when
# set, otherwise whatever is first on PATH, otherwise it probes the standard
# TeX Live / MacTeX / TinyTeX / MiKTeX locations. $TEXBIN prepends one bin
# directory to that search.

set -euo pipefail
shopt -s nullglob

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$SCRIPT_DIR"

usage() {
  cat <<'EOF'
Usage: ./build.sh [main|paper]

  main    build main.tex  (modular source)       -> build-main/main.pdf
  paper   build paper.tex (single-file version)  -> build-paper/paper.pdf
  (default: main)

Environment overrides:
  PDFLATEX  pdflatex executable to use (default: autodetected)
  BIBTEX    bibtex executable to use   (default: autodetected)
  TEXBIN    TeX bin directory to search first
EOF
}

TARGET="${1:-main}"
case "$TARGET" in
  -h|--help) usage; exit 0 ;;
  main|paper) ;;
  *) echo "build.sh: unknown target '$TARGET'" >&2; usage >&2; exit 2 ;;
esac

PDFLATEX_CMD="${PDFLATEX:-pdflatex}"
BIBTEX_CMD="${BIBTEX:-bibtex}"

# Bin directories worth probing when the TeX binaries are not already on PATH.
# Unmatched globs expand to nothing (nullglob above), so the list is safe on
# every platform.
tex_bin_candidates() {
  printf '%s\n' \
    "${TEXBIN:-}" \
    /Library/TeX/texbin \
    "$HOME/Library/TinyTeX/bin/universal-darwin" \
    "$HOME/Library/TinyTeX/bin/$(uname -m)-darwin" \
    "$HOME/.TinyTeX/bin/$(uname -m)-linux" \
    "$HOME/.TinyTeX/bin/x86_64-linux" \
    "$HOME/.TinyTeX/bin/aarch64-linux" \
    /usr/local/texlive/*/bin/* \
    /opt/homebrew/bin \
    /usr/local/bin \
    /usr/bin \
    "/c/Program Files/MiKTeX/miktex/bin/x64" \
    /c/texlive/*/bin/windows
}

if ! command -v "$PDFLATEX_CMD" >/dev/null 2>&1; then
  while IFS= read -r dir; do
    [ -n "$dir" ] && [ -x "$dir/$PDFLATEX_CMD" ] || continue
    PATH="$dir:$PATH"
    export PATH
    break
  done < <(tex_bin_candidates)
fi

for cmd in "$PDFLATEX_CMD" "$BIBTEX_CMD"; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    cat >&2 <<EOF
build.sh: '$cmd' not found.

Install a TeX distribution (TeX Live, MacTeX, TinyTeX or MiKTeX) and either
put its bin directory on PATH or point this script at it:

  PDFLATEX=/path/to/pdflatex BIBTEX=/path/to/bibtex ./build.sh
  TEXBIN=/path/to/texlive/bin/x86_64-linux ./build.sh
EOF
    exit 127
  fi
done

OUT="build-$TARGET"
mkdir -p "$OUT"

# grep exits 1 on no match, which is a normal result here (not a failure).
count() { grep -cE "$1" "$2" 2>/dev/null || true; }

# Three pdflatex passes with bibtex in between. Per-pass failures are reported
# in the summary below rather than aborting the run, so a missing .bbl on the
# first pass is not fatal.
run_pass() {
  local log="$1"
  shift
  "$@" >"$log" 2>&1 || true
}

run_pass "$OUT/pass1.log" "$PDFLATEX_CMD" -interaction=nonstopmode -output-directory="$OUT" "$TARGET.tex"
# bibtex must run from this directory so that reference.bib is found
run_pass "$OUT/bibtex.log" "$BIBTEX_CMD" "$OUT/$TARGET"
run_pass "$OUT/pass2.log" "$PDFLATEX_CMD" -interaction=nonstopmode -output-directory="$OUT" "$TARGET.tex"
run_pass "$OUT/pass3.log" "$PDFLATEX_CMD" -interaction=nonstopmode -output-directory="$OUT" "$TARGET.tex"

echo "--- $TARGET.tex ---"
echo "errors:      $(count '^! ' "$OUT/pass3.log")"
echo "undefined:   $(count 'undefined' "$OUT/pass3.log")"
echo "overfull:    $(count 'Overfull' "$OUT/pass3.log")"
grep -E "Output written" "$OUT/pass3.log" || echo "NO PDF PRODUCED"
echo "--- bibtex ---"
tail -3 "$OUT/bibtex.log"
