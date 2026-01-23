#include <stddef.h>

/*@
  requires n >= 0 && \valid(t + (0 .. n - 1));
  assigns t[0 .. n - 1];
  ensures ((\result != 0) ==> (\forall integer j; (0 <= j && j < n) ==> (t[j] == 0))) && ((\forall integer j; (0 <= j && j < n) ==> (t[j] == 0)) ==> (\result != 0));
*/
int all_zero_array(const int *t, int n) {
  int k = 0;

  /*@
  loop invariant 0 <= k;
  loop invariant k <= n;
  loop invariant \forall integer j; (0 <= j && j < k) ==> (t[j] == 0);
  loop assigns k;
  loop variant n - k;
*/
  while (k < n) {
    if (t[k] != 0) return 0;
    k++;
  }

  return 1;
}
