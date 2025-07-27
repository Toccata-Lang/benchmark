#include "new.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>

void leafFn(Term ref, Term args) {
  Term a0 = pair_make(APP, 0, NUL, SUB);
  Term b = term_new(VAR, 0, port(2, term_loc(a0)));
  Term l2 = pair_make(LAM, 0, a0, b);
  Term l1 = pair_make(LAM, 0, ERA, l2);
  Term l0 = pair_make(LAM, 0, SUB, l1);
  swapStore(port(1, term_loc(a0)), term_new(VAR, 0, port(1, term_loc(l0))));
  store_redex(args, l0);
  return;
}
Term leaf = new_ref(leafFn);

void nodeFn(Term ref, Term args) {
  Term l3 = pair_make(LAM, 0, ERA, NUL);
  Term l2 = pair_make(LAM, 0, SUB, l3);
  Term l1 = pair_make(LAM, 0, SUB, l2);
  Term rgt = term_new(VAR, 0, port(1, term_loc(l1)));
  Term l0 = pair_make(LAM, 0, SUB, l1);
  Term lft = term_new(VAR, 0, port(1, term_loc(l0)));
  Term a1 = pair_make(APP, 0, rgt, SUB);
  Term a0 = pair_make(APP, 0, lft, a1);
  swapStore(port(2, term_loc(l3)), term_new(VAR, 0, port(2, term_loc(a1))));
  swapStore(port(1, term_loc(l2)), a0);
  store_redex(args, l0);
  return;
}
Term node = new_ref(nodeFn);

Term makeNode;
void makeFn(Term ref, Term args) {
  NativeArgs arityArgs = {0, {}};
  args = strictArgs(ref, args, 1, &arityArgs);
  if (arityArgs.count == 1) {
    Term hTrm = arityArgs.args[0];
    switch(term_tag(hTrm)) {
    case I60:
      if (1) {
	int h = get_i60(hTrm);
	Term a = take(port(2, term_loc(args)));
	if (h == 0) {
	  store_redex(a, leaf);
	} else {
	  store_redex(pair_make(APP, 0, new_i60(h - 1), a), makeNode);
	}
      }
      break;

    default:
      print_term("Bad argument to 'make'", hTrm);
      print_term("args", args);
      BOOM("log");
      break;
    }
  }
  return;
}
Term make = new_ref(makeFn);

void makeNodeFn(Term ref, Term args) {
  Term rgtN = pair_make(OPY, OP_ADD, new_i60(1), SUB);
  Term lftN = pair_make(DUP, 0, SUB, rgtN);
  Term dblN = pair_make(OPY, OP_MUL, new_i60(2), lftN);
  Location nLoc = term_loc(lftN);

  Term h = pair_make(DUP, 0, SUB, SUB);
  Location hLoc = term_loc(h);

  Term lftA1 = pair_make(APP, 0, term_new(VAR, 0, port(1, nLoc)), SUB);
  Term lftA0 = pair_make(APP, 0, term_new(VAR, 0, port(1, hLoc)), lftA1);
  Term lft = term_new(VAR, 0, port(2, term_loc(lftA1)));

  Term rgtA1 = pair_make(APP, 0, term_new(VAR, 0, port(2, term_loc(rgtN))), SUB);
  Term rgtA0 = pair_make(APP, 0, term_new(VAR, 0, port(2, hLoc)), rgtA1);
  Term rgt = term_new(VAR, 0, port(2, term_loc(rgtA1)));

  Term nA1 = pair_make(APP, 0, rgt, SUB);
  Term nA0 = pair_make(APP, 0, lft, nA1);
  
  Term l1 = pair_make(LAM, 0, dblN, term_new(VAR, 0, port(2, term_loc(nA1))));
  Term l0 = pair_make(LAM, 0, h, l1);

  store_redex(args, l0);
  store_redex(lftA0, make);
  store_redex(nA0, node);
  store_redex(rgtA0, make);
  return;
}
Term makeNode = new_ref(makeNodeFn);

void sumLeafFn(Term ref, Term args) {
  Term l = pair_make(LAM, 0, SUB, NUL);
  swapStore(port(2, term_loc(l)), term_new(VAR, 0, port(1, term_loc(l))));
  store_redex(args, l);
  return;
}
Term sumLeaf = new_ref(sumLeafFn);

Term sum;

void sumNodeFn(Term ref, Term args) {
  Term s = pair_make(OPX, OP_ADD, NUL, SUB);
  Term l1 = pair_make(LAM, 0, SUB, term_new(VAR, 0, port(2, term_loc(s))));
  Term l0 = pair_make(LAM, 0, SUB, l1);

  Term sumLft = pair_make(APP, 0, term_new(VAR, 0, port(1, term_loc(l0))), SUB);
  Term sumRgt = pair_make(APP, 0, term_new(VAR, 0, port(1, term_loc(l1))), s);
  swapStore(port(1, term_loc(s)), term_new(VAR, 0, port(2, term_loc(sumLft))));
  store_redex(sumRgt, sum);
  store_redex(args, l0);
  store_redex(sumLft, sum);
  return;
}
Term sumNode = new_ref(sumNodeFn);

void sumFn(Term ref, Term args) {
  Term a1 = pair_make(APP, 0, sumLeaf, SUB);
  Term a0 = pair_make(APP, 0, sumNode, a1);
  Term l = pair_make(LAM, 0, a0, term_new(VAR, 0, port(2, term_loc(a1))));

  interact(args, l);
  return;
}
Term sum = new_ref(sumFn);

struct timeval startTime, endTime;
double elapsed;
int height;
u64 expected;

void endFn(Term ref, Term args) {
  NativeArgs arityArgs = {0, {}};
  args = strictArgs(ref, args, 1, &arityArgs);
  if (arityArgs.count == 1) {
    u64 currTop;
    Term rTrm = arityArgs.args[0];
    switch(term_tag(rTrm)) {
    case VAR:
      return;
      break;

    case I60: 
      gettimeofday(&endTime, NULL);
      elapsed = (endTime.tv_sec - startTime.tv_sec) +
	(endTime.tv_usec - startTime.tv_usec) / 1000000.0;

      pair_free(term_loc(args));
      print_term("result", rTrm);
      printf("exptd: %lu\n", expected);
      if (expected != get_i60(rTrm)) {
	abort();
	break;
      }
      break;

    default:
      print_term("bad result", rTrm);
      BOOM("in 'end'");
      break;
    }
  }
  return;
}
Term end = new_ref(endFn);

int main(int argc, char *argv[]) {
  if (argc < 3) {
    printf("\ncorrect command line is \"bench <height> <threads>\"\n");
    exit(1);
  }
  
  // Initialize the VM with some memory
  // hvm_init((u64)3 * (u64)(1 << 30));
  hvm_init(2000);

  height = atoi(argv[1]);
  if (height < 0) {
    printf("\nInvalid height: %d\n", height);
    exit(1);
  } else {
    printf("\nHeight: %d\n", height);
  }
  i64 wtf = 1 << height;
  expected = (wtf - 1) * wtf / 2;

#ifndef SINGLE_THREAD
  threadCount = atoi(argv[2]);
  printf("Threads: %d\n", threadCount);
#else
  printf("Running single thread\n");
#endif

  for(int reps = 0; reps < 1; reps++) {
    hvm_reset();
    printf("run: %d\n", reps);

    gettimeofday(&startTime, NULL);

    Term a1 = pair_make(APP, 0, new_i60(0), SUB);
    Term a0 = pair_make(APP, 0, new_i60(height), a1);

    Term n = term_new(VAR, 0, port(2, term_loc(a1)));
    Term a = pair_make(APP, 0, n, SUB);
    Term a3 = pair_make(APP, 0, term_new(VAR, 0, port(2, term_loc(a))), SUB);

    unsigned i = 0;
    store_redex(a0, make);
    store_redex(a, sum);
    store_redex(a3, end);

    normalize();

    u64 interactions = rdxCount;
    printf("interactions: %lu\n", interactions);
    printf("MIPS: %f\n", interactions / elapsed / 1000000);
    printf("elapsed: %f\n", elapsed);
    printf("Heap needed: %u\n", RNOD_END);
  }

  return 0;
}

char *refName(Term ref) {
  if (ref == leaf)
    return "leaf";
  else if (ref == node)
    return "node";
  else if (ref == make)
    return "make";
  else if (ref == makeNode)
    return "makeNode";
  else if (ref == sumLeaf)
    return "sumLeaf";
  else if (ref == sumNode)
    return "sumNode";
  else if (ref == sum)
    return "sum";
  else if (ref == end)
    return "end";
  else
    return "unknown";
}
