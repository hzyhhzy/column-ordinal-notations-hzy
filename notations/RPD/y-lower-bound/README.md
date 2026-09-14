# RPD with a Y lower-bound annotation · [中文版](README.zh-CN.md)

[Download the standalone NER script](RPD-with-Y-bound.ne-rewritten.js). It retains RPD's fundamental sequences, comparison and six equivalent views, and adds a display-only annotation `RPD ≥ Y【mountain】`. The original [RPD expander](../RPD-mountain.ne-rewritten.js) is unchanged.

Load the complete script into ne-rewritten's custom-notation facility. It registers as **RPD（附 Y 山脉下界）**, ID `rpd-with-y-lower-bound-v1`, separate from the original RPD. If an older annotated version is already installed, replace it instead of enabling a duplicate with the same ID. HTML mode shows the complete Y mountain; plain text shows its column-wise parent list. No build step or external module is required.

The bounded recursive search checks structural certificates before displaying a lower bound. For example, standard RPD `11248` produces the Y word `125354`. Some higher-layer patterns also produce bounds starting with `14`, `15` or higher. These are expansion-rank bounds, not claims of equality, optimal tightness or standardness of the annotation. The new comparison arguments are paper-level work, **not end-to-end Lean-certified theorems**.

## Documentation

- [Detailed algorithm, limits and examples (Chinese)](algorithm.zh-CN.md).
- [Chinese usage guide and manuscript index](README.zh-CN.md).
- [Source provenance and license boundary](SOURCES.md).

The mathematical modules are inlined into the JS file. Names of `.cjs` modules and historical probes in the manuscripts identify development sources, not extra files needed to load this script. The portable check included here is:

```sh
node --max-old-space-size=256 notations/RPD/y-lower-bound/test.cjs
```

Run it from the repository root. It tests registration, preserved RPD operations, representative stronger annotations, SVG output and resource fallbacks without changing browser settings. Finite tests do not prove the comparison lemmas.
