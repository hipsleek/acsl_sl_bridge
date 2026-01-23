#include <stddef.h>

/*@
  requires \valid(array + (0 .. length - 1));
  assigns array[0 .. length - 1];
  ensures \forall size_t j; (0 <= j && j < length && \old(array[j]) == old) ==> (array[j] == new) && \forall size_t j; (0 <= j && j < length && \old(array[j]) != old) ==> (array[j] == \old(array[j]));
*/
void search_replace(int array[], size_t length, int old, int new) {
  /*@
  loop invariant 0 <= i;
  loop invariant i <= length;
  loop invariant \at(i, LoopEntry) <= i;
  loop invariant \forall size_t j; (i <= j && j < length) ==> (array[j] == \at(array[j], LoopEntry));
  loop invariant \forall size_t j; (\at(i, LoopEntry) <= j && j < i && array[j] == old) ==> (array[j] == new);
  loop invariant \forall size_t j; (\at(i, LoopEntry) <= j && j < i && array[j] != old) ==> (array[j] == array[j]);
  loop assigns i, array[\at(i, LoopEntry) .. length - 1];
  loop variant length - i;
*/
  for (size_t i = 0; i < length; ++i) {
    if (array[i] == old) {
      array[i] = new;
    }
  }
}
