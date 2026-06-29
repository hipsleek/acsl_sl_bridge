#include <stddef.h>

/*@
  requires a != b && a != c && b != c && \valid(a) && \valid(b) && \valid(c);
  assigns *a, *b, *c;
  ensures *a == \old(*c) && *b == \old(*a) && *c == \old(*b);
*/
void rotate3(int *a, int *b, int *c) {
  int t = *a;
  *a = *c;
  *c = *b;
  *b = t;
}
