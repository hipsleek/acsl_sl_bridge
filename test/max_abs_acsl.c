#include <limits.h>

/*@
  requires a > INT_MIN && b > INT_MIN;
  assigns \nothing;
  ensures \result >= a && \result >= b && \result >= 0 && \result >= -a && \result >= -b && (\result == a || \result == -a || \result == b || \result == -b);
*/
int max_abs(int a, int b) {
  int aa = (a < 0) ? -a : a;
  int bb = (b < 0) ? -b : b;
  return (aa >= bb) ? aa : bb;
}
