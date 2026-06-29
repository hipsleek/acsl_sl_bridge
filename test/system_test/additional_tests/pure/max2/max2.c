/*@[SL]
  case {
    a>=b ==> ens[r] r==a;
    a<b  ==> ens[r] r==b;
  };
*/
int max2(int a, int b) {
  if (a >= b) {
    return a;
  } else {
    return b;
  }
}

