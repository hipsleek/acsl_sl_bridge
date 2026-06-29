# acsl_sl_bridge

Bridge separation-logic (SL) specifications to **ACSL** so that they can be verified by
[Frama-C](https://frama-c.com/) / WP.

You write a contract in a compact SL dialect inside a special comment:

```c
/*@[SL]
  req p->int*(a);
  ens p->int*(a+1);
*/
void inc(int *p) { (*p)++; }
```

…and the tool turns it into the equivalent ACSL contract:

```c
/*@ requires \valid(p);
    assigns *p;
    ensures *p == \old(*p) + 1; */
```

There are **two front ends** for the same translation:

1. **Frama-C plugin** (`-sl`) — parses the SL in-process and attaches a native ACSL contract,
   so `frama-c -sl -wp file.c` verifies directly. *(recommended)*
2. **Standalone CLI** — translates `file.c` → `file_acsl.c` on disk, then you run Frama-C on the
   output (this is what `sl_to_acsl.sh` automates).

> 📖 **User manual:** [`docs/SL_to_ACSL_Manual.md`](docs/SL_to_ACSL_Manual.md) — the SL syntax
> reference, CLI/GUI walkthrough (with screenshots), and a full appendix of worked translations.
> For the translation internals, see Hrishiraj Mandal's report `acsl_sl_bridge.pdf`.

---

## Prerequisites

Everything lives in an opam switch. Install the toolchain once:

```bash
opam install dune menhir frama-c alt-ergo
why3 config detect            # let WP discover provers (z3/alt-ergo)
```

> **Before running anything** (the helper scripts included), activate the opam switch that has
> Frama-C so that `dune`, `frama-c`, and `ocamlfind` are on your `PATH`:
>
> ```bash
> eval $(opam env)                       # current switch
> # or, if Frama-C is in another switch:
> opam switch <name> && eval $(opam env)
> ```
>
> Verify with `frama-c -version` (expect 32.x, Germanium). The scripts do **not** set this up for
> you — they assume the toolchain is already on `PATH`.

---

## Repository layout

```
src/
  sl_lexer.mll, sl_parser.mly      SL surface syntax  -> Sl_ast
  acsl_lexer.mll, acsl_parser.mly  ACSL surface syntax (reverse direction, scaffolded)
  ast/        sl_ast, core, acsl_ast        ASTs + the neutral Core IR
  ast_printer/                              pretty-printers
  translator/ sl_to_core, core_to_acsl,     the actual translation
              acsl_to_core, core_to_sl
  frontend/   sl_extract.ml                 split a file into code / SL blocks (shared)
  main.ml                                   the standalone CLI
frama_sl/     sl_options, sl_attach, sl_register   the Frama-C plugin
test/system_test/                          example .c inputs + golden _acsl.c outputs
sl_to_acsl.sh        standalone:  translate + run frama-c
install_sl.sh        install the -sl plugin into the Frama-C plugin path
run_sl.sh            run the plugin from _build without installing (dev)
```

---

## Option 1 — Frama-C plugin (`-sl`)

### Install (once, and after editing plugin sources)

```bash
./install_sl.sh
```

This builds and `dune install`s the `frama-c-sl` package, then writes the discovery file
`<libdir>/frama-c/plugins/sl/META` so Frama-C auto-loads the plugin.

### Run

```bash
frama-c -sl file.c                 # parse SL and attach the ACSL contract
frama-c -sl -print file.c          # ...and print the function with its attached contract
frama-c -sl -wp file.c             # ...and verify it with WP
frama-c -sl -wp -wp-no-simpl -wp-no-let file.c    # more readable WP goals
```

Example:

```bash
frama-c -sl -wp test/system_test/incr_max/incr_max_spatial.c
# [sl] attached SL contract to incr_max
# [wp] Proved goals:    8 / 8
```

To see the original SL next to the generated ACSL, add `-sl-show` (printed per function):

```bash
frama-c -sl -sl-show file.c
```

### GUI

```bash
frama-c-gui -sl -wp file.c
```

The lower notebook (next to *Information* / *Messages*) gains an **“SL → ACSL”** tab showing,
per function, the original separation-logic block (left) beside the generated ACSL contract
(right), evenly split, word-wrapped, with keywords highlighted and a **Copy** button per side.

Each function header carries a **proof-status bullet** (● green = proved, red = invalid,
orange = unknown, ○ grey = not yet attempted). The two views are **synced with the source**: click a
function in the main source view to highlight + scroll to its block here, or click a block here to
jump to it in the source. Use **Refresh status** to re-query after running WP.

Functions whose generated ACSL fails to type/attach (e.g. specs using `<limits.h>` macros like
`INT_MAX`) are flagged with **⚠ (not attached)** and a red bullet — the generated ACSL is still
shown for inspection, but no contract was attached to the function.

`-sl-show` remains the console equivalent of this tab. The proof bullets in the source view show
WP results as usual.

### Dev loop without installing

`run_sl.sh` builds the plugin and its libraries in `_build` and loads them with `-load-module`:

```bash
./run_sl.sh -wp test/system_test/additional_tests/pure/max2/max2.c
```

---

## Option 2 — Standalone CLI

Translate only (writes `<name>_acsl.c` next to the input and echoes it):

```bash
eval $(opam env --switch=ocaml5)
dune exec ./src/main.exe -- test/system_test/abs_diff/abs_diff.c
```

Translate **and** run Frama-C/WP in one step:

```bash
./sl_to_acsl.sh test/system_test/incr_max/incr_max_spatial.c          # CLI
./sl_to_acsl.sh --gui test/system_test/incr_max/incr_max_spatial.c    # Frama-C GUI
```

---

## Examples / test suite

`test/system_test/` holds example inputs (`<name>.c`) paired with the expected ACSL
(`<name>_acsl.c`). `additional_tests/` groups extra cases:

```
additional_tests/
  pure/              max2, sign, safe_div          # arithmetic / case-splits, no heap
  single_cell_heap/  inc, rotate3                  # pointer cells, separation
  known_gaps/        global_counter                # documents a current limitation (expected fail)
```

Regenerate every `_acsl.c` and confirm nothing changed versus what is committed:

```bash
eval $(opam env --switch=ocaml5)
find test/system_test -name '*.c' ! -name '*_acsl.c' \
  -exec dune exec ./src/main.exe -- {} \; >/dev/null 2>&1
git diff --stat -- test/system_test     # no output = all outputs match the committed golden files
```

---

## How it works

The translation chain (the plugin reuses stages ①–④ from the CLI verbatim, then attaches the
result instead of writing a file):

```
SL text
  → Sl_parser/Sl_lexer        → Sl_ast.spec          (parse SL)
  → Sl_to_core.sl_to_core     → Core.spec            (neutral IR: phases, frame, aliasing)
  → Core_to_acsl.spec_to_acsl → ACSL text
  ── CLI:    write <name>_acsl.c ; run frama-c
  └─ plugin: Logic_lexer.spec → Logic_typing → Annotations.add_*  (attach typed funspec)
```

The `Core` IR is the hinge: it normalises pre/post (`'` and `@old`), turns heap cells into
`\valid` + `assigns`, and makes separation (`*`) explicit as `!=` facts. A second printer
(`core_to_sl`) renders Core back to SL — the intended hook for future SLEEK integration.

---

## Known limitations

- **Loop contracts are supported.** A `/*@[SL] ... */` block placed directly above a `for`/`while`
  loop is translated to `loop invariant/assigns/variant` and attached to the loop statement
  (e.g. `zero_array` proves 15/15, matching the CLI). A block is routed to a loop or a function
  contract by whichever (loop statement / function definition) appears nearest below it.
- **`'` (prime) notation breaks Frama-C preprocessing**: Frama-C runs its annotation preprocessor
  over `/*@ ... */` comments, and a stray `'` (used by the `*_prime` specs and `for.c`) is read as
  an unterminated character literal, aborting before the plugin runs. Use the non-prime variants
  (`\old`, alias) with the plugin; the standalone CLI handles `'` because it reads the raw source.
- **`<limits.h>` macros** (`INT_MAX`, `INT_MIN`): not expanded for the plugin, so they fail typing
  (e.g. `abs_diff`) — shown as "(not attached)" in the GUI. Same root cause as above; use the CLI.
- **Recursive/inductive predicates** (`x::ll<n>`): not supported by the SL dialect; only the flat
  fragment (single cells `p->int*(v)`, array ranges, arithmetic, case-splits) is translated.
