#include <stddef.h>

/*@
  requires \valid(p);
  assigns *p;
  ensures *p == \old(*p) + 1;
*/
void inc(int *p) {
  (*p)++;
}
