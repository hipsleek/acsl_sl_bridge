#include <stddef.h>

/*@
  requires p != q && \valid(p) && \valid(q);
  assigns *p, *q;
  behavior case1:
    assumes *p >= *q;
    ensures *p == \old(*p) + 1 && *q == \old(*q);
  behavior case2:
    assumes *p < *q;
    ensures *p == \old(*p) && *q == \old(*q) + 1;
  complete behaviors;
  disjoint behaviors;
*/
void incr_max(int *p, int *q) {
  if (*p >= *q) {
    (*p)++;
  } else {
    (*q)++;
  }
}
