#!/usr/bin/env bash
# Build the paper with latexmk (which drives pdflatex + bibtex underneath),
# falling back to an explicit pdflatex/bibtex sequence when latexmk is absent.
#
# JMLR production compiles with latexmk via pdflatex, so pdflatex is the
# toolchain that matters (not XeTeX/tectonic), and latexmk is the driver that
# re-runs passes until the cross-references and the bibliography settle.
#
#   ./build.sh            # build main.tex   (modular source, out: build-main/)
#                         driver: latexmk when installed, else pdflatex x3 + bibtex
#                         (USE_LATEXMK=0 forces the fallback; LATEXMK=... overrides)
#   ./build.sh paper      # build paper.tex  (single file,    out: build-paper/)
#   ./build.sh appendix   # build the online appendix (online-appendix/main.tex,
#                         #                    out: build-appendix/main.pdf)
#   ./build.sh release    # refresh paper.tex from sections/, build it, copy the
#                         # result to ./paper.pdf (the committed PDF), and build
#                         # the online appendix into ./online-appendix.pdf
#   ./build.sh --help
#
# Run `python3 flatten.py` first if you edited sections/*.tex and want the
# single-file version refreshed. The `release` target does this for you.
#
# Portrait of the TeX installation this expects: TinyTeX or TeX Live with
# latexmk, pdflatex and bibtex. A *minimal* TeX installation ships the EC/TC
# (T1/TS1) Computer Modern fonts only as METAFONT sources, and the JMLR style
# needs them -- the `(c)` of the copyright footnote and the itemize bullets are
# typeset in TS1 -- so pdflatex would have to render a bitmap for every size
# used, which needs a writable font tree and the mf engine. Install the Type 1
# releases instead; they have identical metrics, so the output does not change:
#
#   tlmgr install cm-super
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
Usage: ./build.sh [main|paper|appendix|release]

  main      build main.tex  (modular source)       -> build-main/main.pdf
  paper     build paper.tex (single-file version)  -> build-paper/paper.pdf
  appendix  build the online appendix              -> build-appendix/main.pdf
            (online-appendix/main.tex; no bibtex pass, no \bibliography)
  release   refresh paper.tex from main.tex + sections/*.tex via flatten.py,
            build it, and copy the result to ./paper.pdf at the repository
            root; then build the online appendix and copy it to
            ./online-appendix.pdf. Refuses to overwrite ./paper.pdf if the
            build reports errors.
  (default: main)

Environment overrides:
  PDFLATEX      pdflatex executable to use (default: autodetected)
  BIBTEX        bibtex executable to use   (default: autodetected)
  LATEXMK       latexmk executable to use  (default: autodetected)
  USE_LATEXMK   set to 0 to force the explicit pdflatex x3 + bibtex sequence
  TEXBIN        TeX bin directory to search first
EOF
}

TARGET="${1:-main}"
RELEASE=0
SRC_TEX=""
WITH_BIBTEX=1
case "$TARGET" in
  -h|--help) usage; exit 0 ;;
  main|paper) ;;
  appendix) SRC_TEX="online-appendix/main.tex"; WITH_BIBTEX=0 ;;
  release) RELEASE=1; TARGET=paper ;;
  *) echo "build.sh: unknown target '$TARGET'" >&2; usage >&2; exit 2 ;;
esac
[ -n "$SRC_TEX" ] || SRC_TEX="$TARGET.tex"

if [ "$RELEASE" -eq 1 ] && ! command -v python3 >/dev/null 2>&1; then
  cat >&2 <<'EOF'
build.sh: python3 not found, and the `release` target needs it to refresh
paper.tex from main.tex + sections/*.tex. Run `./build.sh paper` instead and
copy build-paper/paper.pdf to ./paper.pdf by hand.
EOF
  exit 127
fi

PDFLATEX_CMD="${PDFLATEX:-pdflatex}"
BIBTEX_CMD="${BIBTEX:-bibtex}"
LATEXMK_CMD="${LATEXMK:-latexmk}"
# USE_LATEXMK=0 forces the explicit pdflatex/bibtex sequence.
USE_LATEXMK="${USE_LATEXMK:-1}"

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

if ! command -v "$PDFLATEX_CMD" >/dev/null 2>&1 || ! command -v "$LATEXMK_CMD" >/dev/null 2>&1; then
  while IFS= read -r dir; do
    [ -n "$dir" ] || continue
    [ -x "$dir/$PDFLATEX_CMD" ] || [ -x "$dir/$LATEXMK_CMD" ] || continue
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

# --- reproducible output -------------------------------------------------
# pdfTeX takes the embedded CreationDate/ModDate from the clock, so rebuilding
# unchanged sources would otherwise produce a different file every time. Pin
# the timestamp here; main.tex pins the trailer /ID for the same reason.
# Together they make the output byte-reproducible, so a rebuilt paper.pdf
# differs only when the paper's content changed. Export SOURCE_DATE_EPOCH
# yourself to override the pinned value.
if [ -z "${SOURCE_DATE_EPOCH:-}" ]; then
  SOURCE_DATE_EPOCH=1789948800   # 2026-09-21T00:00:00Z, the release date
fi
export SOURCE_DATE_EPOCH

# The release target publishes the single-file version, so refresh it from the
# modular sources first; otherwise the committed PDF could silently lag behind
# sections/*.tex.
if [ "$RELEASE" -eq 1 ]; then
  echo "--- flatten (paper.tex from main.tex + sections/*.tex) ---"
  python3 "$SCRIPT_DIR/flatten.py"
fi

# Per-pass failures are reported in the summary below rather than aborting the
# run, so a missing .bbl on the first pass is not fatal.
run_pass() {
  local log="$1"
  shift
  "$@" >"$log" 2>&1 || true
}

STEM="$(basename "${SRC_TEX%.tex}")"
LOG="$OUT/$STEM.log"
BLG="$OUT/$STEM.blg"

if [ "$USE_LATEXMK" -eq 1 ] && command -v "$LATEXMK_CMD" >/dev/null 2>&1; then
  DRIVER="latexmk ($("$LATEXMK_CMD" --version 2>/dev/null | head -1))"
  # The compile flags live in ./latexmkrc; only the bibliography mode is
  # per document, because the online appendix has no \bibliography and latexmk
  # must not go looking for a .bbl it will never find.
  if [ "$WITH_BIBTEX" -eq 1 ]; then
    BIBFLAG="-bibtex"
  else
    BIBFLAG="-bibtex-"
  fi
  # -outdir is repeated here (latexmkrc reads OUTDIR as well) so that the
  # command line alone says where everything goes.
  run_pass "$OUT/latexmk.log" env OUTDIR="$OUT" PDFLATEX="$PDFLATEX_CMD" \
    "$LATEXMK_CMD" -pdf "$BIBFLAG" -outdir="$OUT" "$SRC_TEX"
  [ -f "$LOG" ] || LOG="$OUT/latexmk.log"
else
  DRIVER="$PDFLATEX_CMD (three passes)$([ "$WITH_BIBTEX" -eq 1 ] && printf ' + %s' "$BIBTEX_CMD")"
  run_pass "$OUT/pass1.log" "$PDFLATEX_CMD" -interaction=nonstopmode -output-directory="$OUT" "$SRC_TEX"
  # bibtex must run from this directory so that reference.bib is found
  if [ "$WITH_BIBTEX" -eq 1 ]; then
    run_pass "$OUT/bibtex.log" "$BIBTEX_CMD" "$OUT/$TARGET"
  else
    : > "$OUT/bibtex.log"
  fi
  run_pass "$OUT/pass2.log" "$PDFLATEX_CMD" -interaction=nonstopmode -output-directory="$OUT" "$SRC_TEX"
  run_pass "$OUT/pass3.log" "$PDFLATEX_CMD" -interaction=nonstopmode -output-directory="$OUT" "$SRC_TEX"
  LOG="$OUT/pass3.log"
  BLG="$OUT/bibtex.log"
fi

# When pdfTeX cannot find a font it appends the command kpathsea would need to
# build one to $OUT/missfont.log and stops. In a minimal TeX installation that
# means the EC/TC (T1/TS1) Computer Modern fonts, which the JMLR style needs
# for the copyright footnote and the itemize bullets; name the remedy instead
# of leaving the bare kpathsea error to be decoded.
font_failure_hint() {
  local log="$OUT/missfont.log" names
  [ -f "$log" ] || return 0
  names="$(awk '{print $NF}' "$log" | sort -u | tr '\n' ' ')"
  [ -n "$names" ] || return 0
  cat >&2 <<EOF

build.sh: pdfTeX stopped on font(s) it could not find: $names

  In a minimal TeX installation the EC/TC (T1/TS1) Computer Modern fonts exist
  only as METAFONT sources, so every size used has to be rendered to a bitmap
  first, which needs a writable font tree and the mf engine. Install the Type 1
  releases instead -- identical metrics, so the output does not change:

      tlmgr install cm-super

EOF
}

echo "--- $SRC_TEX ---"
echo "driver:      $DRIVER"
echo "errors:      $(count '^! ' "$LOG")"
echo "undefined:   $(count 'undefined' "$LOG")"
echo "overfull:    $(count 'Overfull' "$LOG")"
grep -E "Output written" "$LOG" || echo "NO PDF PRODUCED"
echo "--- bibliography ---"
if [ -f "$BLG" ]; then
  grep -oE "You've used [0-9]+ entries" "$BLG" || echo "entries:     (not reported)"
  BIB_WARN="$(count 'Warning--' "$BLG")"
  echo "warnings:    $BIB_WARN"
  if [ "$BIB_WARN" != "0" ]; then
    grep -m5 -- 'Warning--' "$BLG" || true
  fi
else
  echo "(none: this document cites nothing)"
fi

if [ ! -f "$OUT/$STEM.pdf" ]; then
  font_failure_hint
  echo "build.sh: no PDF was produced; see $LOG" >&2
  exit 1
fi

# The release target copies the fresh build over the committed paper.pdf, but
# only when the build is clean: a broken or missing PDF never reaches the root.
if [ "$RELEASE" -eq 1 ]; then
  ERRORS="$(count '^! ' "$LOG")"
  SRC="$OUT/$TARGET.pdf"
  if [ "$ERRORS" != "0" ]; then
    echo "release: $ERRORS LaTeX error(s); see $LOG. paper.pdf NOT updated." >&2
    exit 1
  fi
  cp -f -- "$SRC" "$SCRIPT_DIR/paper.pdf"
  echo "--- release ---"
  echo "updated paper.pdf from $SRC ($(wc -c < "$SCRIPT_DIR/paper.pdf" | tr -d ' ') bytes)"
  # The build is reproducible, so a byte-identical result means the paper's
  # content did not change rather than that the build merely repeated itself.
  echo "note: the build is byte-reproducible, so after rebuilding unchanged sources"
  echo "      paper.pdf is unchanged too; 'git status' is a reliable signal."

  # The online appendix is a separate published artifact with the same gates.
  echo "--- online appendix ---"
  if ! "$SCRIPT_DIR/build.sh" appendix; then
    echo "release: online appendix build failed; ./online-appendix.pdf NOT updated." >&2
    exit 1
  fi
  APX_SRC="$SCRIPT_DIR/build-appendix/main.pdf"
  cp -f -- "$APX_SRC" "$SCRIPT_DIR/online-appendix.pdf"
  echo "updated online-appendix.pdf from $APX_SRC ($(wc -c < "$SCRIPT_DIR/online-appendix.pdf" | tr -d ' ') bytes)"
fi
