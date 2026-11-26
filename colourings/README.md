# Colourings

The two colourings of the section "Two colourings" of the paper, with the colours 0 and 1, and programs that check
them. They are not part of the Lean build.

| File | n | What it shows |
|---|---|---|
| `R574_858_points_rule.json` | 858 | R(5,7;4) >= 859: no 5 points with all 4-subsets in colour 0, no 7 points with all 4-subsets in colour 1 |
| `R553_100_points.json`, `R553_100_points.csv` | 100 | R(5,5;3) >= 101: no 5 points with all triples in one colour |

## 4-subsets of the projective line over F_857 (`R574_858_points_rule.json`)

- The points are 0, 1, ..., 856 (the integers mod the prime q = 857) and one more point, infinity, numbered 857;
  so n = q + 1 = 858. The file has the format of the `_rule.json` files of arXiv:2611.25143.
- The entry `table` is a string of 857 characters 0/1. For points a < b < c < d:
  - if d is not infinity, the colour of {a,b,c,d} is table[x] with x = (a-c)(b-d) / ((a-d)(b-c)) mod q;
  - if d is infinity, it is table[x] with x = (a-c) / (b-c) mod q.
  x is never 0 or 1, so those two places of the table are not used.
- The entry `classes_in_colour_0_by_smallest_value` lists the 51 classes of cross-ratio values (out of 143) on which
  the table is 0, each by its smallest element, as printed in the paper.
- SHA-256 of the string `table`: `d5c58d63c0b8320ab89fb4cc76345856b0aa4529c1db653275dc11f181bdd376`.

### The check with less symmetry (`verify_affine.c`, `compat_threads.h`)

It assumes nothing about the table. It goes through every 4-subset of the 858 points and confirms that the maps
x -> x+1 and x -> 3x (infinity stays) keep its colour; 3 is a primitive root mod 857, so these maps generate all
maps x -> ux + v with u != 0, which move any two finite points onto 0 and 1. Every set of 5 or more points has two
finite points, so the program then grows the sets through 0 and 1, point by point in increasing order, and stops a
branch at the first 4-subset of the other colour.

    gcc -O3 -pthread -o verify_affine verify_affine.c
    python3 -c "import json; open('tau858.txt', 'w').write(json.load(open('R574_858_points_rule.json'))['table'])"
    ./verify_affine 857 tau858.txt 5 7 4

The last argument is the number of threads. `compat_threads.h` gives the program the few Windows calls it uses
through pthreads; on Windows it includes `windows.h` instead. On this table, with 4 threads on 2 cores, the program
printed (about 400 seconds):

    INVARIANCE q=857 g=3: 22423156470 4-subsets (all of them), mismatches under z+1: 0, under g*z: 0   [293 s]
    COLOUR 0: sets of 5 points through 0,1: 0   (sets of 4 points in colour 0 through 0,1 that were examined: 129684)
    COLOUR 1: sets of 7 points through 0,1: 0   (sets of 6 points in colour 1 through 0,1 that were examined: 27999760)
    PASS: no such set on the q+1 points   [398 s]

### A second, separately written check (`verify_projective.cpp`, `check_projective.py`)

    python3 check_projective.py

(on Windows: `py -3 check_projective.py`). It needs Python 3 and `g++` or `clang++` with C++17; no Python packages.
`verify_projective.cpp` is the program of the same name in the ancillary files of arXiv:2611.25143, unchanged;
`check_projective.py` is the script of that paper with its list of cases replaced by this table. The script
compiles the program in a temporary directory, compares the table with the digest above, and runs the program. The
program first checks that the field is prime and that the table is constant on each class of cross-ratio values (the
six values x, 1/x, 1-x, 1/(1-x), x/(x-1), (x-1)/x), so that the colouring is unchanged by every projective map. It
then looks at every set of 5 points and every set of 7 points that contains 0, 1 and infinity: 365,085 and
22,110,642,855 sets. Because any three points can be moved to 0, 1 and infinity by a projective map, this is a
complete check. The output must report `forbidden_color0 = 0`, `forbidden_color1 = 0` and `pass = true`. The
program alone: `./verify_projective 857 <table> 5 7`.

## Triples of Z_100 (`R553_100_points.json`, `R553_100_points.csv`)

These two files are the files of the same names prepared for the ancillary files of arXiv:2611.25143, unchanged; in
their entry `status`, "this paper" is arXiv:2611.25143.

- The points are the integers mod 100, numbered 0, ..., 99.
- `.csv`: one row per triple: its three points in increasing order, then its colour. The first row is a header.
  Every triple appears exactly once.
- `.json`: the entry `colouring` is a string of the characters 0 and 1. Character number i, counting from 0, is the
  colour of the i-th triple in lexicographic order: (0,1,2), (0,1,3), ..., (97,98,99). Its SHA-256 is
  `eb3bcc29ec00a29dae1322d87cbf10901832d7ca282c856aa3e6993d6553a6bc`. The entry `rule` holds the group
  (x -> 9^i x + b mod 100) and the 96 orbit representatives printed in the paper.
- `python verify.py R553_100_points.csv 5 5` searches for a forbidden set from the definition and prints PASS.
  Standard library only; a few seconds.
- `python rebuild_from_rule.py R553_100_points.json` rebuilds the colouring from its group and representatives and
  compares it with the stored string.
