# PAGE in Lean

An autoformalization, generated with ChatGPT, of the rotation-system search in Alexander Metzger and Austin Ulrigg’s *An Efficient Genus Algorithm Based on Graph Rotations*. The project also examines the House of Graphs implementation at commit `4b68d24`. [Paper, version 5](https://arxiv.org/abs/2411.07347v5) · [Journal article](https://doi.org/10.1016/j.disc.2026.115308) · [House of Graphs source at the audited revision](https://github.com/SanderGi/Genus/tree/4b68d247240ed0e47c8c6e9f40e83f84330242c1/HoG)

## Main results

- **Exhaustive search.** The Lean solver returns facial walks of a rotation system and maximizes their number over all rotations. For a connected graph, Euler’s formula identifies this optimum with the minimum orientable genus. The theorem `Page.DartGraph.minimum_genus` proves the comparison of Euler expressions in the rotation-system model. [Solver and theorem](Page.lean)
- **House of Graphs.** For a graph of minimum degree at least two, the modeled local tests accept a complete cover of the darts exactly when it gives the faces of a rotation system. The capped search finds a prescribed number of faces exactly when such a rotation exists with every face within the length cap. The model of block decomposition assumes correct workers, genus additivity, and a successful check of the decomposition on the given graph. [Local tests](Page/HoGLocal.lean) · [Capped search](Page/HoGCatalogue.lean) · [Block decomposition](Page/HoGBlocks.lean)
- **A face-length counterexample.** A 21-vertex graph with 27 edges has orientable genus one. Each of its 64 minimum-genus rotations has a face of length 28. Capping face length at 27 raises the minimum among the retained rotations to two. On this input the audited C program reports failure in materialized PAGE-only mode and returns one in low-memory mode. Section 7.2 of the paper allows face lengths up to twice the number of edges. [Lean theorem](HoG.lean) · [Graph, proof, and test data](audit/FaceCap/README.md)
- **Examples from the paper.** A four-spoked wheel witnesses a gap in the low-degree criterion as stated in Proposition 2 of version 5. An embedding of $K_{3,3}$ on the torus shows that both directions of an edge can occur in one face. [Explicit facial walks](Page/PaperWitnesses.lean) · [Notes on the paper](paper-notes.md)

The Lean model abstracts from the C search order, caches, memory operations, and worker selection. The C comparisons below apply to the pinned source revision.

## Build and check

With Lean installed through [elan](https://lean-lang.org/install/), run these commands from this directory. The project selects Lean 4.28.0 and uses only its standard library.

```sh
lake build
lake env lean Check.lean
python3 audit/FaceCap/check.py
```

`Check.lean` prints the axioms used by the main theorems. The exhaustive search theorem uses Lean’s ordinary kernel. The finite bound in `Page.FaceCap.exact_cap_obstruction` checks all 4,096 rotation masks using `native_decide`, which also trusts Lean’s compiler. The Python command independently enumerates the same 4,096 rotations for each of the two graph sizes. A slower [kernel-only replay](audit/FaceCap/kernel_check.py) is available for selected intervals or the full range.

With a C compiler available, `python3 audit/Blocks/check.py` compares the Lean and C block decompositions on every connected labelled simple graph of orders one through five, using two edge insertion orders. The [face-cap audit](audit/FaceCap/README.md) gives commands for testing the pinned C program on both examples. Four additional source-level checks use [CBMC](cmodel/README.md).

The included C source and makefile retain Alexander Metzger’s copyright and the upstream GPL-2.0-only license. See the [source and license details](upstream/README.md).
