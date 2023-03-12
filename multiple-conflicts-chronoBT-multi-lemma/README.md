
Modified Version for Multiple Conflicts Analyzing in Chronological Backtracking and Learning All Lemmas
===============================================================================

Use `./configure && make` to configure and build `cadical` and the library
`libcadical.a` in the default `build` sub-directory.  The header file of
the library is [`src/cadical.hpp`](src/cadical.hpp) and includes an example
for API usage.

The basic build and execution commands in `chronoBT` are:
```bash
$ ./configure
$ make -j
$./build/cadical <DIMACS_FILE>
$ make
```

See [`BUILD.md`](BUILD.md) for options and more details related to the build
process.

See `cadical -h` for more options.

