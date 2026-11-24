# The Genus of Bipartite Kneser Graphs

This folder contains two records from a Lean autoformalization of the quadrangulation construction in Austin Ulrigg and Alexander Metzger’s paper. The Lean source and build logs for this release are unavailable here. [Paper on arXiv](https://arxiv.org/abs/2610.03159)

For every prime $h > 3$ with $h \equiv 3 \pmod 8$, the release reports a rotation system on the bipartite Kneser graph $H(h,2)$. Every face has length four, and the automorphisms of the map act transitively on its vertices. The release treats the passage from rotation systems to orientable cellular embeddings and the genus calculation by Euler’s formula as external mathematical steps.

- The [release summary](validation/release-summary.json) records a successful build with Lean 4.28.0 and mathlib v4.28.0. It names the main theorem, `Kneser.exists_vertex_transitive_quadrangulation`, and lists the axioms it uses. This is the original validation report.
- The [input provenance](SOURCE_PROVENANCE.json) identifies the manuscript, Python programs, and exceptional-prime certificates used for the construction. The recorded hashes for all four upstream code and certificate files match the [cited revision](https://github.com/SanderGi/Genus/tree/4b68d247240ed0e47c8c6e9f40e83f84330242c1/BipartiteKneser).

Alexander Metzger published a separate Lean development in the same repository. Its theorem `BipartiteKneser.optimalRotation_of_prime` constructs a quadrangulation and proves that its genus is minimal among rotation systems. The linked directory contains the source and build instructions for that development. [Lean source](https://github.com/SanderGi/Genus/tree/c0fff826dac4decdae027a221dad81d4849fc125/BipartiteKneser) · [Pull request #7](https://github.com/SanderGi/Genus/pull/7)
