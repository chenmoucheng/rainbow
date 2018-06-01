/*
 * To swap nibble endianness
 */

#include <stdio.h>

int main()
{
  int c,d;

  while ((c = getchar()) != EOF) {
    d = getchar();
    if (d != EOF) {
      putchar(d); putchar(c);
    }
  }

  return 0;
}

