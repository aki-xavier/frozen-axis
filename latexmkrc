# latexmk configuration for this repository. latexmk reads it automatically when
# it runs from the repository root (its documented search order is ./latexmkrc,
# ./.latexmkrc, then $HOME/.latexmkrc), so everything that is common to the build
# targets lives here and build.sh only has to name the source file.
#
# build.sh exports:
#   OUTDIR     the output directory for this target (build-paper/, build-appendix/)
#   PDFLATEX   an alternative pdflatex executable, if the user overrode it
# It also passes -bibtex or -bibtex- on the command line, because the online
# appendix has no bibliography and must not send latexmk looking for one.
#
# Invoked by hand, the same two variables are the only ones that matter:
#
#   OUTDIR=build-paper latexmk -pdf -bibtex paper.tex

$pdf_mode = 1;                                   # pdflatex -> PDF

# -interaction=nonstopmode keeps a typo from parking the build on a prompt, so
# a failure surfaces through the log. -file-line-error is deliberately NOT used:
# it replaces TeX's `! ' error marker with `file:line: ', which also prefixes
# ordinary warnings, and build.sh counts `^! ' lines to report the error count
# and to decide whether a build may be published. Mixing the two formats would
# make that count read zero on a broken build.
$pdflatex = ($ENV{'PDFLATEX'} || 'pdflatex')
          . ' -interaction=nonstopmode %O %S';

# Keep every generated file beside the PDF that was produced from it.
$out_dir = $ENV{'OUTDIR'} if $ENV{'OUTDIR'};

# Run bibtex only when the .aux actually requests a bibliography.
$bibtex_use = 1;

# The file-recorder output makes latexmk's dependency check exact, so it knows
# a rebuild is needed when a section file changes.
$recorder = 1;

# Say what is being run, and stop at the first error rather than looping.
$silent = 0;
$max_repeat = 5;

# Extra files removed by `latexmk -c`.
$clean_ext = 'synctex.gz fdb_latexmk fls out bbl blg';
