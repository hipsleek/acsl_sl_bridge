#include <stddef.h>

/* 1 — Pure: maximum of two integers.
   The case split becomes two ACSL behaviors + complete/disjoint. WP proves it.
   => GREEN */
/*@[SL]
  case {
    a>=b ==> ens[r] r==a;
    a<b  ==> ens[r] r==b;
  };
*/
int max(int a, int b) {
  if (a >= b)
    return a;
  else
    return b;
}

/* 2 — Heap: swap two separate cells.
   a->int*(u) becomes \valid(a); separation a!=b is explicit; pre-state values
   become \old(...); the plugin synthesises assigns *a, *b. WP proves it.
   => GREEN */
/*@[SL]
  req a!=b && a->int*(u) && b->int*(v);
  ens a->int*(v) && b->int*(u);
*/
void swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}

/* 3 — Flagship: pointers + separation + case split.
   Two heap cells and a case analysis -> two behaviors with complete/disjoint
   and an assigns *p, *q frame. WP proves every clause.
   => GREEN */
/*@[SL]
  req p!=q && p->int*(a) && q->int*(b);
  case {
    a>=b ==> ens p->int*(a+1) && q->int*(b);
    a<b  ==> ens p->int*(a) && q->int*(b+1);
  };
*/
void incr_max(int *p, int *q) {
  if (*p >= *q)
    (*p)++;
  else
    (*q)++;
}

/* 4 — Verification catches a bug.
   Same swap spec as #2, but the body has the classic "forgot the temporary"
   bug, so it does not actually swap. The contract still attaches, but WP cannot
   prove the postcondition.
   => ORANGE */
/*@[SL]
  req a!=b && a->int*(u) && b->int*(v);
  ens a->int*(v) && b->int*(u);
*/
void swap_buggy(int *a, int *b) {
  *a = *b;   /* bug: overwrites *a before saving it */
  *b = *a;   /* now both cells hold the old *b, not a true swap */
}
