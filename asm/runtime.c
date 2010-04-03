#include <stdio.h>
#include <stdlib.h>

// Links to closure entry points for the purpose of inspecting
// any structures that are allocated on the heap.

extern int* MkTrip3();
extern int* MkTrip2();
extern int* MkTrip1();
extern int* MkTrip0();
extern int* MkTrip();

extern int* f1();
extern int* f0();
extern int* f();

extern int* top0();
extern int* top();

// A simple, non-collected heap:

#define HEAPLEN 4000
int freeHeap = 0;
int heap[HEAPLEN];

/***
 * Uses the value found one word behind the pointer
 * given to allocate memory in the heap. Returns the address
 * of the allocated memory.
 ***/
int* alloc(int* f)
{
  int size = 1 + *(f - 1);
  if (size + freeHeap > HEAPLEN) {
    fprintf(stderr,"Out of memory!");
    exit(1);
  }

  int* result = heap + freeHeap;
  *result   = (int)f;
  freeHeap += size;

  return result;
}

void dumpHeap() {
  int i = 0;
  printf("Address   Contents\n");
  while (i<freeHeap) {
    int* start = heap+i;
    int* tag   = (int*)(*start);
    int  size  = *(tag - 1);
    i          = i + size + 1;
    printf("%08x: [%08x", start, tag);
    while (size>0) {
      printf(" %08x", *++start);
      size--;
    }
    printf("]\n");
  }
}

int main() {
    int* result;
    printf("Possible object tags:\n");
    printf("MkTrip %08x, MkTrip0 %08x, MkTrip1 %08x\n",
           MkTrip, MkTrip0, MkTrip1);
    printf("MkTrip2 %08x, MkTrip3 %08x\n", MkTrip2, MkTrip3);
    printf("f %08x, f0 %08x, f1 %08x\n", f, f0, f1);
    printf("top %08x, top0 %08x\n", top, top0);
    printf("Starting:\n");
    result = top0();
    printf("Finishing (%d words allocated).\n",freeHeap);
    printf("Result = %08x\n", result);
    dumpHeap();
    return 0;
}
