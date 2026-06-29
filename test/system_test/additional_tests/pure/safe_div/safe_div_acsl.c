/*@
  requires b > 0 && a >= 0;
  assigns \nothing;
  ensures \result == a / b;
*/
int safe_div(int a, int b) {
  return a / b;
}
