#include <stddef.h>

/*@[SL]
    req array->int*(0,length-1) && Term[];
    ens \forall size_t j. 0<=j<length ==> array[j]'==0;
*/
void reset(int* array, size_t length) {
    /*@[SL]
        req array->int*(i,length-1) && i<=length && Term[length-i];
        ens \forall size_t j. (i<=j<=length ==> array[j]'==0) && i'==length;
    */
    for (size_t i = 0; i < length; i++) array[i] = 0;
}