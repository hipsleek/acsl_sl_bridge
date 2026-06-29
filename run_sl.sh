#!/usr/bin/env sh
# Run the SL plugin on a file WITHOUT installing it (loads cmxs from _build).
#
# Requires the opam switch that has Frama-C to be ACTIVE first
# (so dune / frama-c / ocamlfind are on PATH):
#   eval $(opam env)        # or: opam switch <name> && eval $(opam env)
#
# If the plugin is already installed (via ./install_sl.sh) it is auto-loaded by
# Frama-C; loading it again here would fail with "module already loaded", so in
# that case this script just delegates to the installed `frama-c -sl`.
#
# Usage:
#   ./run_sl.sh [frama-c args...] file.c
# Examples:
#   ./run_sl.sh -print test/system_test/additional_tests/pure/max2/max2.c
#   ./run_sl.sh -wp -wp-no-simpl -wp-no-let test/system_test/incr_max/incr_max_spatial.c
set -eu

cd "$(dirname "$0")"

# If already installed, just use it (avoids double-loading the same modules).
if [ -f "$(ocamlfind printconf destdir)/frama-c/plugins/sl/META" ]; then
  exec frama-c -sl "$@"
fi

# Otherwise load the freshly-built modules in dependency order, then the plugin.
B=_build/default
dune build \
  src/ast/ast.cmxs \
  src/frontend/frontend.cmxs \
  src/ast_printer/ast_printer.cmxs \
  src/translator/translator.cmxs \
  src/acsl_sl_bridge_lib.cmxs \
  frama_sl/frama_sl.cmxs

exec frama-c \
  -load-module "$B/src/ast/ast.cmxs" \
  -load-module "$B/src/frontend/frontend.cmxs" \
  -load-module "$B/src/ast_printer/ast_printer.cmxs" \
  -load-module "$B/src/translator/translator.cmxs" \
  -load-module "$B/src/acsl_sl_bridge_lib.cmxs" \
  -load-module "$B/frama_sl/frama_sl.cmxs" \
  -sl "$@"
