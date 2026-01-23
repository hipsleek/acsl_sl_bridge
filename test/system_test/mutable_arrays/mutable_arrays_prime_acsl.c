#include <stddef.h>

/*@
  requires \valid(array + (0 .. length - 1));
  assigns array[0 .. length - 1];
  ensures \forall size_t j; (0 <= j && j < length) ==> (array[j] == 0);
*/
void reset(int* array, size_t length) {
    /*@
  loop invariant i <= length;
  loop invariant 0 <= i;
  loop invariant \at(i, LoopEntry) <= i;
  loop invariant \forall size_t j; (i <= j && j < length) ==> (array[j] == \at(array[j], LoopEntry));
  loop invariant \forall size_t j; (\at(i, LoopEntry) <= j && j < i) ==> (array[j] == 0);
  loop assigns i, array[\at(i, LoopEntry) .. length - 1];
  loop variant length - i;
*/
    for (size_t i = 0; i < length; i++) array[i] = 0;
}
