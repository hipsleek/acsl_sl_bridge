/*@[SL]
case {
  j < 40 => req Term[40 - j]; ens j == 40;
  !(j < 40) => req Term[]; ens j == \old(j);
};
*/

int add_ten(int a)
