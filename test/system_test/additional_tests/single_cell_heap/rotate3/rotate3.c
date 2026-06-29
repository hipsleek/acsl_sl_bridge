#include <stddef.h>

/*@[SL]
  req a!=b && b!=c && a!=c && a->int*(u) && b->int*(v) && c->int*(w);
  ens a->int*(w) && b->int*(u) && c->int*(v);
*/
void rotate3(int *a, int *b, int *c) {
  int t = *a;
  *a = *c;
  *c = *b;
  *b = t;
}
