#include <stddef.h>

/*@[SL]
  req (n >= 0) && t->int*(0, n-1);
  ens (\result != 0) <==> (\forall integer j. (0 <= j && j < n) ==> t[j] == 0);
*/
int all_zero_array(const int *t, int n) {
  int k = 0;

  /*@[SL]
    req (0 <= k && k <= n) && (\forall integer j. (0 <= j && j < k) ==> t[j] == 0) && Term[n - k];
    ens (0 <= k' && k' <= n);
  */
  while (k < n) {
    if (t[k] != 0) return 0;
    k++;
  }

  return 1;
}
