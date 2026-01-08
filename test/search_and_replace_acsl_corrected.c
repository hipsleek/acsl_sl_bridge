#include <stddef.h>

/*@
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall size_t i; 0 <= i < n ==> 
    ( \old(a[i]) == old_val ==> a[i] == new_val ) &&
    ( \old(a[i]) != old_val ==> a[i] == \old(a[i]) );
*/
void search_replace(int a[], size_t n, int old_val, int new_val) {
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall size_t j; 0 <= j < i ==> 
      ( \at(a[j], LoopEntry) == old_val ==> a[j] == new_val ) &&
      ( \at(a[j], LoopEntry) != old_val ==> a[j] == \at(a[j], LoopEntry) );
    loop invariant \forall size_t j; i <= j < n ==> 
      a[j] == \at(a[j], LoopEntry);
    loop assigns i, a[0 .. n-1];
    loop variant n - i;
  */
  for (size_t i = 0; i < n; ++i) {
    if (a[i] == old_val) {
      //@ assert a[i] == old_val;
      a[i] = new_val;
      //@ assert a[i] == new_val;
    }
  }
}