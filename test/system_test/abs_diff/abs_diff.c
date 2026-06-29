#include <limits.h>

/*@[SL]
  req (a < b ==> b - a <= INT_MAX) && (b <= a ==> a - b <= INT_MIN);
  ens[r] (a < b ==> a + r == b) && (b <= a ==> a - r == b);
*/
int diff_from_a_to_b(int a, int b) {
    if (a < b) {
        return b - a;
    } else {
        return a - b;
    }
}

