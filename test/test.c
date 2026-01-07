/*@[SL]
  ensures \result == a + 9;
*/
int add_ten(int a)
{
  /*@[SL]
    loop invariant 0 <= i <= 10;
    loop invariant a == \at(a,LoopEntry) + i - \at(i,LoopEntry);
    loop assigns i, a;
    loop variant 10 - i;
  */
  for (int i = 1; i < 10; ++i) {
    ++a;
  }

  return a;
}