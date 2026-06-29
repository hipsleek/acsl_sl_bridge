#include <stddef.h>

/*@[SL]
  req p->int*(a);
  ens p->int*(a+1);
*/
void inc(int *p) {
  (*p)++;
}
