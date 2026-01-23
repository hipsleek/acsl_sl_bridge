#include <limits.h>

/*@
  requires ((a < b) ==> (b - a <= INT_MAX)) && ((b <= a) ==> (a - b <= INT_MIN));
  assigns \nothing;
  ensures ((a < b) ==> (a + \result == b)) && ((b <= a) ==> (a - \result == b));
*/
int diff_from_a_to_b(int a, int b) {
    if (a < b) {
        return b - a;
    } else {
        return a - b;
    }
}
