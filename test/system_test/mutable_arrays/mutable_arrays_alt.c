#include <stddef.h>

/*@[SL]
    req array->int*(_,0,length-1) && Term[];
    ens array->int*(arr,0,length-1) && \forall size_t j . 0<=j<length ==> arr[j]==0;
*/
void reset(int* array, size_t length) {
    /*@[SL]
        req array->int*(_,i,length-1) && i<=length && Term[length-i];
        ens array->int*(arr,i,length-1) && \forall size_t j . (i<=j<length ==> arr[j]==0) && i'==length;
    */
    for (size_t i = 0; i < length; i++) array[i] = 0;
}