#include <stddef.h>

/*@
  requires len >= 0 && \valid(t + (0 .. len - 1));
  assigns \nothing;
  behavior case1:
    assumes \exists integer i; 0 <= i && i < len && t[i] == elt;
    ensures 0 <= \result && \result < len && \old(t[\result]) == elt;
  behavior case2:
    assumes \forall integer i; (0 <= i && i < len) ==> (t[i] != elt);
    ensures \result == -1;
  complete behaviors;
  disjoint behaviors;
*/
int search_present_absent(const int *t, int len, int elt) {
  /*@
  loop invariant 0 <= i;
  loop invariant i <= len;
  loop invariant \forall integer j; (0 <= j && j < i) ==> (t[j] != elt);
  loop assigns i;
  loop variant len - i;
*/
  for (int i = 0; i < len; i++) {
    if (t[i] == elt) return i;
  }
  return -1;
}
