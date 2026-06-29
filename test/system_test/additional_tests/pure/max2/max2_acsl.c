/*@
  requires \true;
  assigns \nothing;
  behavior case1:
    assumes a >= b;
    ensures \result == a;
  behavior case2:
    assumes a < b;
    ensures \result == b;
  complete behaviors;
  disjoint behaviors;
*/
int max2(int a, int b) {
  if (a >= b) {
    return a;
  } else {
    return b;
  }
}
