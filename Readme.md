
To compile and run:

clang -O3 -g -o bench -latomic bench.c new.c && ./bench 15 4

The first parameter to the `bench` program is the height of the tree.
The second parameter is the number of threads you want to use.