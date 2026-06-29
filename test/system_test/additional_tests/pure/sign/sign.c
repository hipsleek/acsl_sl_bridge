/*@[SL]
  case {
    x>0  ==> ens[r] r==1;
    x==0 ==> ens[r] r==0;
    x<0  ==> ens[r] r==-1;
  };
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
