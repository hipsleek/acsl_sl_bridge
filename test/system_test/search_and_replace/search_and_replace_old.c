#include <stddef.h>

/*@[SL]
req array->int*(0,length-1) && Term[];
ens (\forall size_t j. (0<=j<length && \old(array[j])==old ==> array[j]==new))
 && (\forall size_t j. (0<=j<length && \old(array[j])!=old ==> array[j]==\old(array[j])));
*/
void search_replace(int array[], size_t length, int old, int new) {
  /*@[SL]
  req array->int*(i,length-1) && Term[length - i];
  ens i' == length 
    && (\forall size_t j. (i<=j<length && \old(array[j])==old ==> array[j]==new))
    && (\forall size_t j. (i<=j<length && \old(array[j])!=old ==> array[j]==\old(array[j])));
  */
  for (size_t i = 0; i < length; ++i) {
    if (array[i] == old) {
      array[i] = new;
    }
  }
}
