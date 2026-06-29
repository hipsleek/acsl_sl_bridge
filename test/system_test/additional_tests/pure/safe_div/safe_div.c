/*@[SL]
  req b > 0 && a >= 0;
  ens[r] r == a / b;
*/
int safe_div(int a, int b) {
  return a / b;
}
