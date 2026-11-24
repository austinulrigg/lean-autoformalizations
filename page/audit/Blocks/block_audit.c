/* Compare the unmodified source's actual static functions against Lean.
   Each record preserves block order, vertex numbering, and adjacency order. */
#define main upstream_genus_main
#include "../../upstream/genus.c"
#undef main

int main(void) {
    for (int n = 1; n <= 5; n++) {
        int endpoints[10][2];
        int count = 0;
        for (int u = 0; u < n; u++) {
            for (int v = u + 1; v < n; v++) {
                endpoints[count][0] = u;
                endpoints[count++][1] = v;
            }
        }
        for (int mask = 0; mask < (1 << count); mask++) {
            for (int order = 0; order <= 1; order++) {
                hog_graph_t g = {0};
                if (!hog_graph_init(&g, n)) return 1;
                for (int i = 0; i < count; i++) {
                    int j = order ? count - 1 - i : i;
                    if ((mask & (1 << j)) &&
                        !hog_graph_add_edge(&g, endpoints[j][0], endpoints[j][1])) return 1;
                }
                int connected = hog_graph_is_connected(&g);
                if (connected < 0) return 1;
                if (connected) {
                    int bridge = hog_graph_has_bridge(&g);
                    hog_block_list_t blocks = {0};
                    if (bridge < 0 || !hog_biconnected_blocks(&g, &blocks)) return 1;
                    printf("[%d,%d,%d,%d,[", n, mask, order, bridge);
                    for (int i = 0; i < blocks.count; i++) {
                        hog_graph_t *b = &blocks.graphs[i];
                        printf("%s[", i ? "," : "");
                        for (int v = 0; v < b->n; v++) {
                            printf("%s[", v ? "," : "");
                            for (int j = 0; j < b->degree[v]; j++) {
                                printf("%s%d", j ? "," : "", b->adj[v][j]);
                            }
                            printf("]");
                        }
                        printf("]");
                    }
                    puts("]]");
                    hog_block_list_free(&blocks);
                }
                hog_graph_free(&g);
            }
        }
    }
    return 0;
}
