/*@
  requires a != b && \valid(a) && \valid(b);
  assigns *a, *b;
  behavior case1:
    assumes a == b;
    ensures *a == \old(*a);
  behavior case2:
    assumes a != b;
    ensures *a == \old(*b) && *b == \old(*a);
  complete behaviors;
  disjoint behaviors;
*/
void swap(int* a, int* b){
    int tmp = *a;
    *a = *b;
    *b = tmp;
}
