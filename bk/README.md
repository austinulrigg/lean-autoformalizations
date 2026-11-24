# The genus of bipartite Kneser graphs

This is the Lean autoformalization of Theorem 1.1 of *The Genus of Bipartite Kneser Graphs* by Austin Ulrigg and Alexander Metzger. The proof and certificate code come from Alexander Metzger’s merged pull request in the Genus repository, at commit `c0fff826dac4decdae027a221dad81d4849fc125`. [Paper](https://arxiv.org/abs/2610.03159) · [Original pull request](https://github.com/SanderGi/Genus/pull/7) · [Source at this revision](https://github.com/SanderGi/Genus/tree/c0fff826dac4decdae027a221dad81d4849fc125/BipartiteKneser)

## What Lean proves

The vertices of $H(h,2)$ are two copies of the two-element subsets of an $h$-element set. Vertices in opposite copies are adjacent when their subsets are disjoint. For every prime $h>3$ with $h\equiv3\pmod 8$, `BipartiteKneser.optimalRotation_of_prime` gives a vertex-transitive quadrangular rotation system on this graph. It attains the minimum orientable genus among all cyclic neighbor orders,

$$
1-\frac{h(h-1)}{2}+\frac{h(h-1)(h-2)(h-3)}{16}.
$$

Lean defines the genus of a rotation by its facial walks and Euler’s formula. The usual correspondence between rotation systems and orientable cellular embeddings gives the surface interpretation. A second theorem, `exists_optimalRotation_gt`, proves that admissible primes exceed every bound. [Main theorems](lean/KneserConstruction/MainTheorem.lean) · [Definition of minimum genus](lean/BipartiteKneser/Genus.lean)

The proof checks explicit witnesses for the seven admissible primes below 131. For larger primes it uses the uniform construction, whose finite boundary calculation covers 4,096 patterns in one case and 16,384 in the other. The Python generator supplies numerical witnesses for the small primes. Lean checks that they have the required properties. [Small primes](lean/BipartiteKneser/SmallPrimes.lean) · [Boundary calculation](lean/KneserConstruction/BoundaryData.lean) · [Certificates](exceptional_certificates.json)

## Build and check

From this directory, with Python 3.10 or later and Lean’s toolchain manager installed, run the following commands. The project selects Lean 4.36.0 and its matching mathlib revision. [Lean installation instructions](https://lean-lang.org/install/)

```sh
lake exe cache get
lake build
lake lint
lake test
```

The tests check the main theorem’s type, reject an altered rotation, and check the axioms used by the main results. The only axioms they allow are `propext`, `Classical.choice`, and `Quot.sound`. [Lean tests](lean/CheckProof.lean)

To run the separate Python certificate checks and regression tests, use the standard Python interpreter with assertions enabled.

```sh
python3 verify_all.py
python3 test_certificates.py
```

This copy passed a clean build, lint checks, and theorem tests with Lean 4.36.0 on Apple Silicon. All 18 Python regression tests passed, and the certificate checks reproduced the saved upstream results byte for byte. Metzger’s pull request also reports independent replay of the two exported theorems in Lean’s kernel and Nanoda. [Upstream verification](https://github.com/SanderGi/Genus/pull/7) · [Saved certificate results](https://github.com/SanderGi/Genus/blob/c0fff826dac4decdae027a221dad81d4849fc125/BipartiteKneser/results/verification.json)

The proof sources and certificate code are distributed under the upstream GNU General Public License, version 2 only. [License](LICENSE)
