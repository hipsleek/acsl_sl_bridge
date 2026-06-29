#!/usr/bin/env sh
# Install the SL plugin into the Frama-C plugin search path so that
#   frama-c -sl <file.c>
# works directly (no -load-module flags). Re-run after editing plugin sources.
#
# Requires the opam switch that has Frama-C to be ACTIVE first
# (so dune / frama-c / ocamlfind are on PATH):
#   eval $(opam env)        # or: opam switch <name> && eval $(opam env)
set -eu

cd "$(dirname "$0")"

# Build and install the frama-c-sl package (libraries + plugin cmxs + METAs).
dune build @install
dune install frama-c-sl

# dune does not currently populate the cross-package plugin *site* file, so we
# create the one discovery META by hand. It points Frama-C at the installed
# findlib package, which resolves all dependency cmxs in order.
SITE="$(ocamlfind printconf destdir)/frama-c/plugins/sl"
mkdir -p "$SITE"
printf 'requires = "frama-c-sl.plugin"\n' > "$SITE/META"

# Same for the GUI side: only frama-c-gui scans plugins_gui, so the CLI binary
# never loads the GTK code.
SITE_GUI="$(ocamlfind printconf destdir)/frama-c/plugins_gui/sl-gui"
mkdir -p "$SITE_GUI"
printf 'requires = "frama-c-sl.gui"\n' > "$SITE_GUI/META"

echo "Installed into: $SITE"
echo "            and $SITE_GUI"
echo "Try:"
echo "  frama-c -sl -print test/system_test/additional_tests/pure/max2/max2.c"
echo "  frama-c -sl -wp -wp-no-simpl -wp-no-let test/system_test/incr_max/incr_max_spatial.c"
