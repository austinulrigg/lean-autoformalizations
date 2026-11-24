# Checks on the C source

Run the following command from the PAGE project directory with CBMC 6.11.0, `goto-cc`, and `goto-instrument` on the path.

```sh
python3 cmodel/verify.py
```

The script verifies the checksum of the pinned C source and generates the GOTO model in a temporary directory with `LONG` defined, as in the upstream makefile. It checks that the resulting program contains both PAGE entry points and the dispatcher, then runs four harnesses with loop-unwinding assertions enabled.

| Harness | Property checked |
| --- | --- |
| `degree_switch` | Full-cycle checking and incremental turn insertion take their fast path when the graph’s maximum degree is at most five. |
| `within_word` | Detection of opposite turns agrees with the defining condition on arbitrary prefixes of length at most twelve, including the degree-two exception. |
| `small_components` | A single chain can be extended, closed, or rolled back as prescribed for local degrees from two through six at graph maximum degree six. |
| `lower_bound` | The rounded Euler lower bound has the specified value across the source parameter types. |

The [original run output](observed.txt) records success on all four harnesses. These results concern the stated functions and bounds. The native executable, the Lean model, and the independent Python enumeration have separate reproduction commands in the [project README](../README.md).
