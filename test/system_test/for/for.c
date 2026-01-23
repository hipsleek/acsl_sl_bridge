/*@[SL]
    ens[r] r == a + 10;
*/
int add_ten(int a){
  /*@[SL]
    req i<=10 && Term[10-i];
    ens i'==10 && a'==a+(i'-i);
  */
  for (int i = 0; i < 10; ++i) ++a;
  return a;
}
