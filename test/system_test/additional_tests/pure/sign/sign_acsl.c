/*@
  requires \true;
  assigns \nothing;
  behavior case1:
    assumes x > 0;
    ensures \result == 1;
  behavior case2:
    assumes x == 0;
    ensures \result == 0;
  behavior case3:
    assumes x < 0;
    ensures \result == -1;
  complete behaviors;
  disjoint behaviors;
*/
int sign(int x) {
  if (x > 0) {
    return 1;
  }
  if (x < 0) {
    return -1;
  }
  return 0;
}
