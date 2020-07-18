This directory contains an optimized function `judge` for the task Substrings.

The theory `Defs.thy` contains the basic definitions for the task
using the library `HOL-Library.Sublist".

The theory `Official.thy` contains my solution for the official task.
Its function `judge` runs in quadratic time.

The theory `Optimized.thy` contains an optimized function `judge` that works
for strings of the same length together with a proof of its
functional correctness. The function `judge` runs in linear time.

The file `gen.cpp` is a simple generator for a pair of strings satisfying
the given property. It is supposed to be called as follows: `gen n`,
and outputs two lines, each containing a string of length `2 * (n + 1)`.

You can use the provided `Makefile` to export and compile the verified code
of the functions `judge` from both theories and benchmark their runtime.
