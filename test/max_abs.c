#include <limits.h>

/*@[SL]
req (a > INT_MIN) && (b > INT_MIN);
ens[r] (r >= 0) &&
       (r >= a && r >= -a && r >= b && r >= -b) &&
       (r == a || r == -a || r == b || r == -b);
*/
int max_abs(int a, int b) {
  int aa = (a < 0) ? -a : a;
  int bb = (b < 0) ? -b : b;
  return (aa >= bb) ? aa : bb;
}
