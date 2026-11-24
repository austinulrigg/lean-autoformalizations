# Pisanski’s conjecture on quadrilateral embeddings

This is an AI-generated Lean 4 autoformalization of the construction in Alexander Metzger and Austin Ulrigg, *Resolving Pisanski’s Conjecture on Quadrilateral Embeddings*. [Paper (arXiv:2610.13085v2)](https://arxiv.org/abs/2610.13085v2)

## What Lean proves

For every $m\ge d\ge 4$ with $4\mid md$, there exists a connected simple $d$-regular bipartite graph with $m$ vertices in each part and a cyclic order of the incident edges at each vertex. Following the resulting face permutation from any dart returns to that dart after four steps and visits four distinct vertices. This is the rotation-system construction in Theorem 1.1. [Main theorem](Pisanski.lean) · [Definitions of the graph and its facial walks](Pisanski/Graph.lean)

```lean
theorem Pisanski.pisanski {m d : Nat}
    (hd : 4 ≤ d) (hdm : d ≤ m) (hadm : 4 ∣ m * d) :
    Pisanski.HasQuadrangulation m d
```

The formal proof ends with the rotation system. The paper applies the classical rotation principle to obtain an orientable cellular embedding and Euler’s formula to compute its genus as $1+m(d-4)/4$. It also uses Euler’s formula for the converse, that such an embedding requires $4\mid md$.

## Where to read the proof

| Result | Lean source |
|---|---|
| Numbering the vertices and checking connectivity and four-step facial walks | [Basic](Pisanski/Basic.lean), [Graph](Pisanski/Graph.lean) |
| Quadrangulation criterion for Haar graphs (Lemma 3.2) | [Haar](Pisanski/Haar.lean) |
| Dihedral constructions (Propositions 4.2 and 4.3) | [Dihedral](Pisanski/Dihedral.lean) |
| Cyclic construction for $4\mid d$ (Proposition 5.1) | [Cyclic](Pisanski/Cyclic.lean), [CyclicArithmetic](Pisanski/CyclicArithmetic.lean), [Modular](Pisanski/Modular.lean) |
| Coverage of all admissible pairs | [Pisanski](Pisanski.lean) |

## Reproduce the checks

With Lean’s toolchain manager installed, run these commands in the `pisanski` directory. The project selects Lean 4.28.0 and uses its bundled standard library. [Lean installation instructions](https://lean-lang.org/install/)

```sh
lake build
lake env lean Check.lean
```

Both commands passed in a clean build. The second prints the main theorem and the axioms used by it and the Haar-graph lemma. Lean reported `propext`, `Classical.choice`, and `Quot.sound` for each. The same command checks the four examples $(m,d)=(4,4),(6,6),(8,5),(7,4)$. [Check file](Check.lean)
