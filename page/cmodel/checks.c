/* Source-level properties of the upstream program, checked by CBMC.
   The renamed CLI stays in the translation unit; worker definitions are original. */
#define main hog_cli_main
#include "../upstream/genus.c"
#undef main

static uint8_t symbolic_byte(void) { uint8_t x; __CPROVER_havoc_object(&x); return x; }
static uint16_t symbolic_word(void) { uint16_t x; __CPROVER_havoc_object(&x); return x; }
static uint32_t symbolic_count(void) { uint32_t x; __CPROVER_havoc_object(&x); return x; }

void check_degree_switch(void) {
    vertex_degree = symbolic_byte();
    __CPROVER_assume(vertex_degree <= 5);
    cycle_length_t length = symbolic_word();
    vertex_t center = symbolic_word();
    degree_t in = symbolic_byte(), out = symbolic_byte();
    /* NULL makes an accidental read before either fast return detectable. */
    __CPROVER_assert(cycle_try_add_rotation_system(NULL, length), "full-cycle check skips on max degree at most five");
    __CPROVER_assert(rotation_transition_add(center, in, out), "incremental insertion skips on max degree at most five");
    cycle_remove_rotation_system(NULL, length);
    rotation_transition_remove(center, in, out);
}

void check_within_word(void) {
    vertex_t path[12];
    degree_t degree = symbolic_byte();
    vertex_degrees = &degree;
    unsigned n = symbolic_byte();
    __CPROVER_assume(n <= 12);
    for (unsigned i = 0; i < 12; ++i) path[i] = symbolic_word();
    const vertex_t prev = symbolic_word(), next = symbolic_word();
    bool reverse_occurs = false;
    for (unsigned j = 0; j + 2 < n; ++j)
        reverse_occurs |= (path[j] == next && path[j+1] == 0 && path[j+2] == prev);
    __CPROVER_assert(path_has_reverse_transition(path, n, prev, 0, next) ==
        (degree > 2 && reverse_occurs), "opposite transition in this prefix, with the degree-two exception");
}

void check_small_components(void) {
    /* One vertex of a graph with global maximum six. Other vertices never accessed. */
    vertex_t succ[6], pred[6];
    degree_t size = symbolic_byte();
    __CPROVER_assume(2 <= size && size <= 6);
    vertex_degree = 6;
    vertex_degrees = &size;
    rotation_next = succ;
    rotation_prev = pred;
    degree_t count = 0;
    rotation_pair_count = &count;
    for (unsigned i = 0; i < 6; ++i) succ[i] = pred[i] = MAX_VERTICES;
    for (unsigned i = 0; i + 1 < size; ++i) {
        __CPROVER_assert(rotation_transition_add(0, i, i + 1), "can extend one simple local chain");
        bool closed = rotation_transition_add(0, i + 1, 0);
        __CPROVER_assert(closed == (i + 2 == size), "closes this chain exactly when the full star is present");
        if (closed) rotation_transition_remove(0, i + 1, 0);
        __CPROVER_assert(succ[i+1] == MAX_VERTICES && pred[0] == MAX_VERTICES && count == i+1,
                         "rejected or removed closing turn leaves the open chain intact");
    }
}

void check_lower_bound(void) {
    vertex_t n = symbolic_word();
    edge_t m = symbolic_word();
    cycle_index_t upper = symbolic_count();
    int64_t gap = (int64_t)m - n + 2 - upper;
    int64_t lower = genus_lower_bound_from_fit_upper_bound(upper, n, m);
    __CPROVER_assert(lower >= 0 && 2 * lower >= gap &&
        (lower == 0 || 2 * (lower-1) < gap), "Euler lower bound is the least nonnegative integer satisfying the inequality");
}
