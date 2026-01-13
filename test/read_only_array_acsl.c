#include <stddef.h>

/*@
  requires \valid_read(array + (0 .. length - 1));
  assigns \nothing;
  behavior case1:
    assumes \exists size_t off; 0 <= off && off < length && array[off] == element;
    ensures array <= \result && \result < array + length && \old(*\result) == element;
  behavior case2:
    assumes \forall size_t off; (0 <= off && off < length) ==> (array[off] != element);
    ensures \result == NULL;
  complete behaviors;
  disjoint behaviors;
*/
int* search(int* array, size_t length, int element) {

  /*@
  loop invariant 0 <= i;
  loop invariant i <= length;
  loop invariant \forall size_t j; (0 <= j && j < i) ==> (\at(array[j], LoopEntry) != element);
  loop assigns i;
  loop variant length - i;
*/
  for (size_t i = 0; i < length; i++) {
    if (array[i] == element) return &array[i];
  }
  return NULL;
}
