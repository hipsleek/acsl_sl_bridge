/*@[SL]
    case {
        a==b ==> req a->int*(u); ens a->int*(u);
        a!=b ==> req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);
    };
*/
void swap(int* a, int* b){
    int tmp = *a;
    *a = *b;
    *b = tmp;
}