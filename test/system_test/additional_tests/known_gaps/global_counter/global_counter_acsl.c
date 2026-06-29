/* Known-gap probe (WP result: 2/4 — fails by design).
   Root cause: a bare scalar (here the global g) is treated as a timeless logical
   variable, not as mutable state. Two defects surface in the generated contract:

     assigns \nothing;       <- g is not a heap atom (p->int*), so the frame
                                computation in sl_to_core.ml:mk_assigns ignores it.
                                (The loop-contract path does collect scalar AsVar;
                                the function-contract path does not.)
     ensures g == g + 1;     <- both g' (post) and g (pre) collapse to plain `g`.
                                The prime/\old phase machinery only fires on heap
                                derefs (*p), never on bare scalar names, so the
                                postcondition becomes a contradiction.

   Expected fix: in the function-contract path, recognise primed scalars that name
   globals / by-ref params, emit C.AsVar for the frame, and apply Pre/Post phases
   to bare scalars (as the loop path already does). */
int g;

/*@
  requires \true;
  assigns \nothing;
  ensures g == g + 1;
*/
void increase(void) {
  g = g + 1;
}
