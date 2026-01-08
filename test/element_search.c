#include <stddef.h>

/*@[SL]
req (len >= 0) && t->int*(0, len-1);
case {
  (\exists integer i. (0 <= i && i < len) && t[i] == elt)
  ==> ens[r] (0 <= r && r < len && t[r] == elt);

  (\forall integer i. (0 <= i && i < len) ==> t[i] != elt)
  ==> ens[r] r == -1;
};
*/
int search_present_absent(const int *t, int len, int elt) {
  /*@[SL]
  req (0 <= i && i <= len) &&
      (\forall integer j. (0 <= j && j < i) ==> t[j] != elt) &&
      Term[len - i];
  ens (0 <= i' && i' <= len);
  */
  for (int i = 0; i < len; i++) {
    if (t[i] == elt) return i;
  }
  return -1;
}
