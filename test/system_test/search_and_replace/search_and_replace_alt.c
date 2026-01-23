#include <stddef.h>

/*@[SL]
    req array->int*(arr,0,length-1) && Term[];
    ens array->int*(narr,0,length-1)
        && (\forall size_t j. 0<=j<length && arr[j]==old ==> narr[j]==new)
        && (\forall size_t j. 0<=j<length && arr[j]!=old ==> narr[j]==arr[j]);
*/
void search_replace(int array[], size_t length, int old, int new) {
  /*@[SL]
    req array->int*(arr,i,length-1) && Term[length-i];
    ens array->int*(narr,i,length-1) && i'==length
        && (\forall size_t j. i<=j<length && arr[j]==old ==> narr[j]==new)
        && (\forall size_t j. i<=j<length && arr[j]!=old ==> narr[j]==arr[j]);
  */
  for (size_t i = 0; i < length; ++i) {
    if (array[i] == old) {
      array[i] = new;
    }
  }
}
