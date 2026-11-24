# A bridgeless failure of the materialized PAGE worker

The input `G21.g6` has orientable genus 1. Every minimum-genus rotation has a face of length 28, whereas the graph has 27 edges. The materialized PAGE worker in the pinned public HoG source stops generating faces at the number of edges. Its search therefore misses every optimum. The same family supplies a 129-vertex example on which the default executable also reports failure.

## Construction

Take two disjoint copies of the bipartite graph obtained from $K_{3,3}$ by deleting one edge. Write $x_i,z_i$ for the endpoints of the missing edge in copy $B_i$. Add two edges, $f=z_1z_2$ and $e=x_1x_2$, to form the cubic graph $H$. In $G_L$ replace $e$ by a path of $L$ edges. Then $n=11+L$ and $m=17+L$. For the graph6 files, the parts in $B_1$ are $\{0,1,2\}$ and $\{3,4,5\}$, with edge $03$ missing. Add 6 to each label for $B_2$. The connectors are $3$–$9$ and the path $0,12,13,\ldots,10+L,6$ when $L\ge2$.

Each $B_i$ contains a spanning six-cycle (on the first copy one such cycle is $0,4,1,3,2,5,0$). Deleting any one vertex leaves that copy connected. The two connectors have distinct ends in each copy. Deleting any vertex of $H$ therefore leaves a connection between the surviving halves. The edge $e$ is on a cycle. Deleting any new path vertex in $G_L$ leaves the two remaining pieces of the path attached to the connected graph $H-e$. Deleting an original vertex retains connectivity as well, since $H$ is 2-connected. Thus $G_L$ is 2-connected and bridgeless.

## Why the genus is 1

$H$ contains a subdivision of $K_{3,3}$. Keep $B_1$ and complete its missing edge using $e$, a path in $B_2$ from $x_2$ to $z_2$, and $f$. Hence $H$ is nonplanar. The graph $K_{3,3}$ with one edge deleted is planar. For example, draw its spanning six-cycle on the sphere, and draw one of the two remaining chords on each side. Join the planar copies by the bridge $f$ to embed $H-e$ on the sphere. A handle between small face regions incident with $x_1$ and $x_2$ allows $e$ to be inserted. Thus the orientable genus is 1. Subdivision preserves the rotations and genus because every new degree-two vertex has only one cyclic order.

## Why one face uses the whole path twice

Suppose a genus-one rotation of $H$ had its two darts of $e$ in distinct faces. Deleting $e$ merges those two faces, so the induced rotation of $H-e$ still has genus one. Indeed its edge and face counts have each decreased by one, and the graph stays connected. The merged face $W$ contains both $x_1$ and $x_2$.

The edge $f$ is a bridge in $H-e$. For any fixed rotations on $B_1$ and $B_2$, inserting the two ends of $f$ into their respective cyclic orders splices one face from each side into a single face, leaving all other faces untouched. This follows by tracing the facial successor across $f$ in each direction. It gives $F(H-e)=F(B_1)+F(B_2)-1$ for the induced rotations. With $E(H-e)=E(B_1)+E(B_2)+1$ and $V(H-e)=V(B_1)+V(B_2)$, Euler's formula gives $g(H-e)=g(B_1)+g(B_2)$ for these specific rotations. Here $g$ denotes the genus of the chosen rotation.

Only the spliced face meets both copies, so it is $W$. Splitting $W$ at $f$ yields a face in each $B_i$ containing both $x_i$ and $z_i$. If either induced rotation were planar, the missing edge $x_i z_i$ could be drawn inside that face, producing a planar embedding of $K_{3,3}$. Each induced genus is consequently at least one, in conflict with their sum being one. This proves that both darts of $e$ lie in one face in every minimum-genus rotation.

In the corresponding face of $G_L$ the path is traversed once in each direction. Between its two traversals there is one nonempty closed detour from each endpoint back to itself. The endpoint has degree three and the facial successor uses a different neighbor, so each detour must leave the endpoint by an edge outside the path. No detour can have length 1 or 2 in a simple graph with nonbacktracking facial walks. Both detours lie in $H-e$, which is bipartite because its two bipartite halves are joined by a bridge. Thus each detour has length at least 4. The face has length at least $2L+8$, strictly greater than $m=L+17$ when $L\ge10$.

## Independent finite check

There are twelve cubic vertices, two cyclic orders per cubic vertex, and one cyclic order at each subdivision vertex. The script checks all $2^{12}=4096$ rotations. For each dart $(u,v)$ it advances to $(v,w)$, where $w$ follows $u$ at $v$. The orbits give the facial walks. It works on the 12-vertex cubic graph, counting a traversal of the subdivided edge as $L$ darts. It verifies the number of darts and applies Euler's formula to each rotation.

| Path length | $n$ | $m$ | Genus-one face lengths for all 64 optima | Rotations surviving the cap |
|---:|---:|---:|---|---|
| 10 | 21 | 27 | 4, 4, 4, 4, 10, 28 | 736, all of genus 2 |
| 118 | 129 | 135 | 4, 4, 4, 4, 10, 244 | 736, all of genus 2 |

In either graph, the respective numbers of rotations of genera 1, 2 and 3 are 64, 1920 and 2112. The cap therefore raises the least genus among the retained embeddings from 1 to 2.

## Reproduce the source behavior

Use the bundled unmodified upstream C and its makefile. From the project directory, with Python 3, `make` and a C compiler, run

```sh
make -C upstream
python3 audit/FaceCap/check.py --genus upstream/genus
```

The finite check also runs on its own with `python3 audit/FaceCap/check.py`. `observed.txt` records the results. Search for `max_search_cycle_length = num_edges` in the pinned source to locate the upper endpoint of the materialized face-generation loop. On bridgeless inputs the wrapper calls `hog_run_page_block` directly. This path preserves the degree-two vertices.

| Public program mode | 21 vertices | 129 vertices |
|---|---|---|
| Materialized PAGE (`--page-only -j 1`) | Exit 1, no genus returned | Exit 1, no genus returned |
| Low-memory PAGE (`--page-only --low-mem -j 1`) | Exit 0, genus 1 | Exit 0, genus 1 |
| Default workers (`-j 1`) | Exit 0, genus 1 | Exit 1, no genus returned |

The default makefile compiles with `-DLONG`, giving MultiGenus a 128-vertex ceiling. On 129 vertices, the default dispatcher can start only materialized PAGE. Its diagnostic includes an unsuccessful-fit message followed by the number `2`. The result parser recognizes specific genus phrases or an integer at the start of the scratch output. It rejects the diagnostic, and the command reports failure. In these tests the public executable never presented 2 as its returned genus.

In a temporary copy we changed only the assignment from `num_edges` to `2 * num_edges`, then compiled with the same makefile. The materialized worker returned genus 1 on both examples. Reproduce this experiment with `python3 audit/FaceCap/check.py --compare-caps` from the project root. This command verifies the pinned C checksum and performs both builds in a temporary directory. These tests fit the 16-bit length counters. A general implementation change to the full $2m$ range would also have to accommodate counter widths and arithmetic throughout the program.

The archived paper already allows $t\le k\le2m$ in §7.2. The specific cutoff in the audited public program conflicts with that section. Both examples use maximum degree three and contain no bridge, so their failure does not depend on the low-degree local-rotation test or the handling of bridges. These runs concern the pinned public source. The private production build and its flags would need separate evidence.

[Upstream source at the audited commit](https://github.com/SanderGi/Genus/blob/4b68d247240ed0e47c8c6e9f40e83f84330242c1/HoG/genus.c) · [Metzger and Ulrigg, arXiv:2411.07347v5, §7.2](https://arxiv.org/html/2411.07347v5#S7.SS2)
