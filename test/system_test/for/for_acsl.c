/*@
  requires \true;
  assigns \nothing;
  ensures \result == a + 10;
*/
int add_ten(int a){
  /*@
  loop invariant i <= 10;
  loop invariant a == \at(a, LoopEntry) + (i - \at(i, LoopEntry));
  loop assigns a, i;
  loop variant 10 - i;
*/
  for (int i = 0; i < 10; ++i) ++a;
  return a;
}
