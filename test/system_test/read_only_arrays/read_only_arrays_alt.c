#include <stddef.h>

/*@[SL]
  req array->int*(arr,0,length-1)@I && Term[];
  case {
    (\exists size_t off . 0<=off<length && arr[off]==element) ==> ens[r] r>=array && r<array+length && arr[r-array]==element;
    (\forall size_t off . (0<=off<length ==> arr[off]!=element)) ==> ens[r] r==NULL;
  };
*/
int* search(int* array, size_t length, int element) {

  /*@[SL]
    req array->int*(arr,0,length-1)@I && 0<=i<=length && Term[length-i] && \forall size_t j. (0<=j<i ==> arr[j]!=element);
    ens i'==length || \return#(array+i') && arr[i']==element /\ 0<=i'<length;
  */
  for (size_t i = 0; i < length; i++) {
    if (array[i] == element) return &array[i];
  }
  return NULL;
}
