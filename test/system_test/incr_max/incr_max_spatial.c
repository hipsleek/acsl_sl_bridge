#include <stddef.h>

/*@[SL]
  req p!=q && p->int*(a) && q->int*(b);
  case {
    a>=b ==> ens p->int*(a+1) && q->int*(b);
    a<b  ==> ens p->int*(a) && q->int*(b+1);
  };
*/
void incr_max(int *p, int *q) {
  if (*p >= *q) {
    (*p)++;
  } else {
    (*q)++;
  }
}
