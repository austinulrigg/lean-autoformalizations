# multi_genus in Lean

This is a copy of the Lean autoformalization from Alexander Metzger’s pull request for Gunnar Brinkmann’s `multi_genus` algorithm. The upstream Lean files credit the Genus contributors. The copy is pinned to commit `c42ab0de7fd0350bb09f766ead81a040dd8ee105`. [Original pull request](https://github.com/SanderGi/Genus/pull/8) · [Source at this revision](https://github.com/SanderGi/Genus/tree/c42ab0de7fd0350bb09f766ead81a040dd8ee105/MultiGenus)

## What Lean proves

For every finite, nonempty, connected simple graph, `MultiGenus.solve_correct` states that the Lean search returns a cyclic order of the neighbors at each vertex and the least genus realized by any rotation system on the graph. If the returned rotation has $F$ face cycles, its genus $g$ satisfies $V-E+F=2-2g$. The isolated vertex is included. The theorem applies to the executable search defined in Lean. The original C solvers are tested separately upstream. [Main theorem](lean/MultiGenus/Solver.lean)

## Build and run

From this `multi_genus` directory, with Lean’s toolchain manager installed, run the following commands. The build uses the pinned versions of Lean and mathlib, both 4.36.0. [Lean installation instructions](https://lean-lang.org/install/)

```sh
lake exe cache get
lake build
lake test
lake lint
lake env lean --run lean/RunMultiGenus.lean graphs/k3-3.mc
```

The final command runs the solver on the included $K_{3,3}$ and prints its genus, 1, and a rotation system in JSON. The pull request reports that the build, tests, and lint checks passed. The test file checks the main theorem’s statement and restricts its axiom dependencies to `propext`, `Classical.choice`, and `Quot.sound`. For this copy all 28 Lean files were compared byte for byte with the pinned revision. The Lean 4.36.0 build result is the one reported upstream. [Test file](lean/CheckMultiGenus.lean) · [Upstream verification](https://github.com/SanderGi/Genus/pull/8)

## Citation and license

Gunnar Brinkmann, “A practical algorithm for the computation of the genus,” *Ars Mathematica Contemporanea* **22** (2022), P4.01. [Paper](https://doi.org/10.26493/1855-3974.2320.c2d)

The Lean sources are copyright © 2026 Genus contributors, distributed under the GNU General Public License, version 2 only. [License](LICENSE)
