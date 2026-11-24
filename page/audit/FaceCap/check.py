"""Verify the face-length obstruction using only the Python 3 standard library.

Run: python3 check.py [--genus /absolute/path/to/genus]
The bundled graph6 files are checked against the vertex labels in README.md.
"""
import argparse
import hashlib
from collections import Counter
from pathlib import Path
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
RAIL = (0, 6)


def graph_edges(length):
    edges = {(i + off, j + off)
             for off in (0, 6) for i in range(3) for j in range(3, 6)
             if (i, j) != (0, 3)}
    edges.add((3, 9))
    rail = [0, *range(12, 11 + length), 6]
    edges.update(tuple(sorted(pair)) for pair in zip(rail, rail[1:]))
    return edges


def graph6(n, edges):
    if n <= 62:
        header = [n]
    else:
        assert n <= 258047
        header = [63, (n >> 12) & 63, (n >> 6) & 63, n & 63]
    bits = [int((i, j) in edges) for j in range(n) for i in range(j)]
    bits.extend([0] * (-len(bits) % 6))
    chunks = [sum(bit << (5 - j) for j, bit in enumerate(bits[i:i + 6]))
              for i in range(0, len(bits), 6)]
    return bytes(x + 63 for x in header + chunks) + b'\n'


def check_rotations(length):
    # The six possible linear orders at a cubic vertex give two cyclic orders.
    # Every new degree-two vertex has just one cyclic order.
    edges = graph_edges(1)
    neighbors = [[] for _ in range(12)]
    for u, v in edges:
        neighbors[u].append(v)
        neighbors[v].append(u)
    for row in neighbors:
        row.sort()
        assert len(row) == 3
    vertex_count = 11 + length
    edge_count = 17 + length
    counts = Counter()
    allowed_counts = Counter()
    shortest_max_face = {}
    optimum_lengths = set()
    for mask in range(1 << 12):
        successor = {}
        for v, row in enumerate(neighbors):
            step = -1 if (mask >> v) & 1 else 1
            for slot, u in enumerate(row):
                successor[u, v] = (v, row[(slot + step) % len(row)])
        unused = set(successor)
        lengths = []
        while unused:
            start = next(iter(unused))
            current = start
            face_size = 0
            while current in unused:
                unused.remove(current)
                face_size += length if current in (RAIL, RAIL[::-1]) else 1
                current = successor[current]
            assert current == start
            lengths.append(face_size)
        assert sum(lengths) == 2 * edge_count
        numerator = 2 - vertex_count + edge_count - len(lengths)
        assert numerator >= 0 and numerator % 2 == 0
        genus = numerator // 2
        counts[genus] += 1
        if genus == 1:
            optimum_lengths.add(tuple(sorted(lengths)))
        longest = max(lengths)
        shortest_max_face[genus] = min(shortest_max_face.get(genus, longest), longest)
        if longest <= edge_count:
            allowed_counts[genus] += 1
    assert sum(counts.values()) == 4096
    assert min(counts) == 1 and min(allowed_counts) == 2
    assert shortest_max_face[1] == 2 * length + 8
    print(f'L={length}   vertices={vertex_count}   edges={edge_count}')
    print('  rotations by genus', dict(sorted(counts.items())))
    print('  rotations with every face of length at most m', dict(sorted(allowed_counts.items())))
    print('  shortest attainable longest face in genus 1', shortest_max_face[1])
    print('  genus-one face-length multisets', sorted(optimum_lengths))


def compare_caps():
    source_dir = HERE.parents[1] / 'upstream'
    source = (source_dir / 'genus.c').read_bytes()
    digest = 'f032b259c5efff9c92f43108887bcd90ff56fc95afa950d80452a5b97a9a0513'
    if hashlib.sha256(source).hexdigest() != digest:
        raise ValueError('The pinned upstream source checksum does not match.')
    old = b'cycle_length_t max_search_cycle_length = num_edges;'
    new = b'cycle_length_t max_search_cycle_length = 2 * num_edges;'
    assert source.count(old) == 1
    # Both test inputs satisfy 2*m <= 270. No signed or 16-bit length limit is reached.
    with tempfile.TemporaryDirectory() as work:
        for label, content in [('original', source), ('experimental-2m', source.replace(old, new))]:
            build = Path(work) / label
            build.mkdir()
            (build / 'genus.c').write_bytes(content)
            shutil.copyfile(source_dir / 'makefile', build / 'makefile')
            subprocess.run(['make', 'genus'], cwd=build, check=True)
            for n in [21, 129]:
                payload = (HERE / f'G{n}.g6').read_bytes()
                command = [str(build / 'genus'), '--page-only', '-j', '1']
                run = subprocess.run(command, input=payload, capture_output=True, timeout=60)
                print(f'{label}: G{n}.g6 exit {run.returncode}')
                print(run.stdout.decode().strip())
                if run.stderr:
                    print(run.stderr.decode().strip())
                if label == 'original':
                    assert run.returncode == 1 and b'0 succeeded, 1 failed' in run.stdout
                else:
                    assert run.returncode == 0 and b'Graph 1 has genus 1' in run.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--genus', type=Path, help='Optional compiled upstream HoG/genus executable')
    parser.add_argument('--compare-caps', action='store_true',
                        help='Compile temporary upstream and modified workers, then replay both inputs')
    options = parser.parse_args()
    for length in [10, 118]:
        check_rotations(length)
        payload = graph6(11 + length, graph_edges(length))
        name = f'G{11 + length}.g6'
        assert (HERE / name).read_bytes() == payload, name
        if options.genus:
            for flags in [[], ['--page-only'], ['--page-only', '--low-mem']]:
                command = [str(options.genus.resolve()), '-j', '1', *flags]
                run = subprocess.run(command, input=payload, capture_output=True, timeout=60)
                print(' ', ' '.join(command), f'[{name}] exit {run.returncode}')
                print('   ', run.stdout.decode().strip().replace('\n', '\n    '))
                if run.stderr:
                    print('   ', run.stderr.decode().strip())
    if options.compare_caps:
        compare_caps()


if __name__ == '__main__':
    main()
