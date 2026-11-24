# Lean autoformalizations in topological graph theory

These projects use Lean to check statements about graph embeddings and orientable genus. The Pisanski and PAGE formalizations were generated with ChatGPT. Each project identifies its main theorems, the corresponding mathematics, and the checks that were run.

| Project | Contents |
| --- | --- |
| [Pisanski’s conjecture](pisanski/) | A rotation system giving a quadrangulation for every admissible pair of parameters. Includes the Lean proof and four examples. |
| [PAGE](page/) | Correctness of an exhaustive rotation-system search, results about the House of Graphs implementation, and a counterexample to a face-length cutoff in the cited revision. |
| [Bipartite Kneser graphs](bk/) | Alexander Metzger’s Lean autoformalization constructs a vertex-transitive quadrangulation of $H(h,2)$ for every prime $h>3$ with $h\equiv3\pmod 8$ and proves its genus is minimum among all rotation systems. Includes the proof, construction code, and certificates. |
| [multi_genus](multi_genus/) | A snapshot of the Lean solver and proof from Alexander Metzger’s pull request on Gunnar Brinkmann’s genus algorithm. |

Each project has its own build instructions and pinned Lean version.
