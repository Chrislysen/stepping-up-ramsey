# Improving the stepping-up lemma for hypergraph Ramsey numbers: formal proofs and colourings

[![Lean proofs](https://github.com/Chrislysen/stepping-up-ramsey/actions/workflows/lean.yml/badge.svg)](https://github.com/Chrislysen/stepping-up-ramsey/actions/workflows/lean.yml)
[![Colouring checks](https://github.com/Chrislysen/stepping-up-ramsey/actions/workflows/colourings.yml/badge.svg)](https://github.com/Chrislysen/stepping-up-ramsey/actions/workflows/colourings.yml)

This repository accompanies the paper

> Christian Lysenstøen (University of Inland Norway), *Improving the stepping-up lemma for hypergraph Ramsey
> numbers, with proofs verified in Lean*, 2026. arXiv link: to be added.

It holds the paper's ancillary files:

- `Proofs/`: the proofs, in Lean 4 with Mathlib, of Theorems A-D, of the proposition on two input colourings and of
  the remarks listed below;
- `colourings/`: the two colourings of the section "Two colourings", for R(5,7;4) >= 859 and R(5,5;3) >= 101, and
  programs that check them. They are not part of the Lean build.

## Results and their Lean theorems

Each theorem is proved in the file `Proofs/<theorem name>.lean`.

| Result in the paper | Lean theorem | File |
|---|---|---|
| Theorem A | `stepping_up_four_to_five_additive_palette` | [`Proofs/stepping_up_four_to_five_additive_palette.lean`](Proofs/stepping_up_four_to_five_additive_palette.lean) |
| Theorem B(i) | `parity_stepping_up_from_five` | [`Proofs/parity_stepping_up_from_five.lean`](Proofs/parity_stepping_up_from_five.lean) |
| Theorem B(ii) | `near_caterpillar_stepping_up_from_five` | [`Proofs/near_caterpillar_stepping_up_from_five.lean`](Proofs/near_caterpillar_stepping_up_from_five.lean) |
| Theorem B(iii) | `split_window_stepping_up` | [`Proofs/split_window_stepping_up.lean`](Proofs/split_window_stepping_up.lean) |
| Theorem B(iv) | `tri_fallback_stepping_up` | [`Proofs/tri_fallback_stepping_up.lean`](Proofs/tri_fallback_stepping_up.lean) |
| Theorem C | `six_uniform_small_threshold_step` | [`Proofs/six_uniform_small_threshold_step.lean`](Proofs/six_uniform_small_threshold_step.lean) |
| Remark after Theorem C (weaker hypothesis on the other colours) | `six_uniform_mixed_small_threshold_step` | [`Proofs/six_uniform_mixed_small_threshold_step.lean`](Proofs/six_uniform_mixed_small_threshold_step.lean) |
| Theorem D(i) | `rank_gap_stepping_up_sharp_red` | [`Proofs/rank_gap_stepping_up_sharp_red.lean`](Proofs/rank_gap_stepping_up_sharp_red.lean) |
| Theorem D(ii) | `odd_split_stepping_up_sharp` | [`Proofs/odd_split_stepping_up_sharp.lean`](Proofs/odd_split_stepping_up_sharp.lean) |
| Theorem D(ii) with 2s_b + k + 1 | `odd_split_stepping_up` | [`Proofs/odd_split_stepping_up.lean`](Proofs/odd_split_stepping_up.lean) |
| Remark: Theorem D(ii) is sharp for its colouring | `odd_split_sharpness_example` | [`Proofs/odd_split_sharpness_example.lean`](Proofs/odd_split_sharpness_example.lean) |
| Theorem D(iii) | `six_uniform_sharp_thin_split` | [`Proofs/six_uniform_sharp_thin_split.lean`](Proofs/six_uniform_sharp_thin_split.lean) |
| Theorem D(iv), first part | `seven_uniform_nine_step` | [`Proofs/seven_uniform_nine_step.lean`](Proofs/seven_uniform_nine_step.lean) |
| Theorem D(iv), second part | `seven_uniform_eleven_step` | [`Proofs/seven_uniform_eleven_step.lean`](Proofs/seven_uniform_eleven_step.lean) |
| Remark on k = 3 | `stepping_up_caterpillar` | [`Proofs/stepping_up_caterpillar.lean`](Proofs/stepping_up_caterpillar.lean) |
| Remark on one fallback colour | `caterpillar_palette_all_uniformities` | [`Proofs/caterpillar_palette_all_uniformities.lean`](Proofs/caterpillar_palette_all_uniformities.lean) |
| Remark on one fallback colour, variant | `stepping_up_one_fallback_all_palettes` | [`Proofs/stepping_up_one_fallback_all_palettes.lean`](Proofs/stepping_up_one_fallback_all_palettes.lean) |
| Proposition (two input colourings, k = 3) | `stepping_up_two_colourings` | [`Proofs/stepping_up_two_colourings.lean`](Proofs/stepping_up_two_colourings.lean) |

Three of the theorems imply others: `six_uniform_mixed_small_threshold_step` implies
`six_uniform_small_threshold_step`, `caterpillar_palette_all_uniformities` implies
`stepping_up_one_fallback_all_palettes`, and `odd_split_stepping_up_sharp` (with h = 0) implies
`odd_split_stepping_up`. Both members of each pair are included.

### How the statements read

- [`Proofs/Defs.lean`](Proofs/Defs.lean) defines the predicate used in every statement, in the namespace `Solon`:
  `Solon.NoMono c t k i` says that every `k`-element set contains a `t`-element subset whose colour under `c` is not
  `i`. So `t` is the subset size (the paper's uniformity) and `k` the set size, the reverse of the paper's letters.
- `X` is any type with a linear order and finitely many elements. Points of the cube are functions `X → Bool`. A
  colouring is a function on all finite subsets; only its values on sets of the relevant size matter.
- Each theorem but `odd_split_sharpness_example` states that for every colouring satisfying the hypotheses there is
  a colouring `ψ : Finset (X → Bool) → C` of the cube satisfying the conclusion, and each proof constructs `ψ`
  explicitly. `odd_split_sharpness_example` is an example for one colouring.
- Statements for two colours use `Fin 2`, with colour `0` in the role of the paper's colour a.
- Every theorem file imports `Proofs.Defs` and nothing else, and `Proofs/Defs.lean` imports Mathlib. The theorem
  files repeat auxiliary definitions under the same names, so they are not meant to be imported together.

## Building the proofs

- Lean: `leanprover/lean4:v4.35.0` (file [`lean-toolchain`](lean-toolchain)).
- Mathlib: tag `v4.35.0` (file [`lakefile.toml`](lakefile.toml)); the exact revisions of Mathlib and its
  dependencies are pinned in [`lake-manifest.json`](lake-manifest.json).

With [elan](https://github.com/leanprover/elan) installed, run in the root of this repository:

```
lake exe cache get
lake build
```

`lake exe cache get` downloads a compiled Mathlib; without it, `lake build` compiles Mathlib from source, which takes
much longer. To build one theorem only, name its module, for example:

```
lake build Proofs.stepping_up_four_to_five_additive_palette
```

To see the axioms a theorem uses, add the line `#print axioms <theorem name>` at the end of its file and build that
module. For each of the eighteen theorems this prints exactly `propext`, `Classical.choice` and `Quot.sound`.

The workflow "Lean proofs" runs `lake exe cache get` and `lake build` on every push.

## The colourings

The two colourings use the colours 0 and 1. [`colourings/README.md`](colourings/README.md) describes the file
formats and what each check does. The workflow "Colouring checks" runs every command below on every push.

### R(5,5;3) >= 101: the triples of Z_100

Files: [`colourings/R553_100_points.csv`](colourings/R553_100_points.csv) (one row per triple, then its colour) and
[`colourings/R553_100_points.json`](colourings/R553_100_points.json) (the colouring as a string, with its group
x -> 9^i x + b mod 100 and the 96 orbit representatives of colour 0). No 5 points have all their triples in one
colour. The SHA-256 digest of the colouring string is
`eb3bcc29ec00a29dae1322d87cbf10901832d7ca282c856aa3e6993d6553a6bc`.

Standard library only, a few seconds:

```
cd colourings
python verify.py R553_100_points.csv 5 5
python rebuild_from_rule.py R553_100_points.json
```

The first searches for a forbidden set from the definition and prints `PASS`; the second rebuilds the colouring from
its group and representatives and compares it with the stored string.

### R(5,7;4) >= 859: the 4-subsets of the projective line over F_857

File: [`colourings/R574_858_points_rule.json`](colourings/R574_858_points_rule.json). The points are 0, ..., 856 and
infinity, numbered 857. The colour of a 4-subset is given by a table of 857 entries at its cross-ratio. No 5 points
have all their 4-subsets in colour 0, and no 7 points have all their 4-subsets in colour 1. The SHA-256 digest of the
table string is `d5c58d63c0b8320ab89fb4cc76345856b0aa4529c1db653275dc11f181bdd376`.

A check through 0, 1 and infinity (Python 3 and `g++` or `clang++` with C++17; about 30 minutes on one core):

```
cd colourings
python3 check_projective.py
```

It must end with `PASS`. A second, separately written check that assumes nothing about the table (about seven minutes
on four threads; the last argument is the number of threads):

```
cd colourings
gcc -O3 -pthread -o verify_affine verify_affine.c
python3 -c "import json; open('tau858.txt', 'w').write(json.load(open('R574_858_points_rule.json'))['table'])"
./verify_affine 857 tau858.txt 5 7 4
```

It must end with `PASS: no such set on the q+1 points`.

## Licences

- Code: the Lean files and the Lake configuration, the C, C++ and Python programs, and the workflows are released
  under the MIT licence; see [`LICENSE`](LICENSE).
- Data and text: the colouring files (`colourings/*.json`, `colourings/*.csv`) and the text of `README.md` and
  `colourings/README.md` are released under the
  [Creative Commons Attribution 4.0 International licence (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/);
  see [`LICENSE-DATA`](LICENSE-DATA).

## How to cite

Please cite the paper (see also [`CITATION.cff`](CITATION.cff)):

```
@misc{Lysenstoen2026SteppingUp,
  author = {Christian Lysenst{\o}en},
  title  = {Improving the stepping-up lemma for hypergraph {R}amsey numbers, with proofs verified in {L}ean},
  year   = {2026},
  note   = {arXiv id to be added}
}
```
