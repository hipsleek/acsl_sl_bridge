/*@[SL]
    ens (*a)'==(*b) && (*b)'==(*a);
*/
void swap(int* a, int* b){
    int tmp = *a;
    *a = *b;
    *b = tmp;
}