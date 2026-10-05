# DQDN packaging validation · [中文版](validation.zh-CN.md)

The final bounded replay during 2026-10-06 integration passed. The [machine-readable receipt](../../tools/dqdn-validation.json) pins all 30 packaged implementation/test files and records the seven completed commands. The [provenance manifest](../../notations/DQDN/provenance.json) separately records 34 imported files and their adaptations.

Run from a fresh clone, with Python and Node on PATH:

```sh
python -B tests/dqdn.py
python -B tools/check_release.py
python -B notations/DQDN/standard.py "TOP[1][1]" --expand 3
```

The test entry point also works from another working directory. No external research directory, NER checkout, Python package or private path is needed. Existing repository-wide checks still verify the other notation snapshots and Lean receipts; they do not compile a new DQDN proof.

Repository release checking passed: **217 Markdown files, 50 unchanged PDFs, 2,177 local links and 21 pinned NER snapshots**. All 11 existing Lean receipt scopes, covering 338 distinct modules, remain current. A fresh full Lean build still requires fetching 12 pinned external BMS source entries; that pre-existing dependency boundary is not a DQDN build or proof. `git diff --check` passed.

## Replayed checks

| Check | Result | Child time |
| --- | --- | ---: |
| Core, type builder, substitution/domain audit, public frontend | 41 Python tests | 3.094 s |
| Ordinal-source macros, small-rank witnesses, type-reuse and extraction interfaces | 43 Python tests | 31.578 s |
| Python fixtures | 1,763,645 bytes generated | 1.125 s |
| Python/NER comparison | 188 parents, 1,504 one-step expansions; 1,614 construction records, all 28 rule kinds | 0.547 s |
| Minimal path and growth view | 106 expressions, 665 least-index steps | 0.406 s |
| Requested power paths | 12 length/count round trips | 0.203 s |
| Three-view table | 18 main and 23 early-second-layer rows | 0.187 s |

The source-tree tests include deliberately guarded cases and assert the expected resource failures; a guarded long trace is not reported as a completed expansion. The early-rank tests replay lower witnesses, **not** a universal ordinal upper-bound classification. View round trips validate the displayed columns, not the ordinal labels.

Each child has a 45-second timeout and is waited for; Python shared-budget checkpoints additionally enforce 40 seconds and 768 MiB peak RSS. Observed Python peaks were 31.62 and 155.27 MiB for the two suites. Node runs with a 512-MiB heap limit. Output is capped at 16 MiB and every sample/trace has a fixed iteration, DAG or step budget. All seven processes exited, with no background search left running. This is not a claim that Node's whole process RSS was measured by its heap limit.

## Unchanged NER behavior

The script SHA-256 remains `b25e394be74f9351b899598e559aaf7367c3833d810a25a7b764dd184c3529c6`. ID is `dqdn-20261005-init-v2`; the default lengths remain `[1,4,2,18,1,0]`. All four views, exact BigInt atoms, standard-domain rejection and clear resource errors are retained. The large ω^ω example is tested by manual path, not restored to defaults.

The standalone VM registration check exercises the NER-shaped API. It is **not** a live browser click/import test. The historical outside-checkout host-source test is not included in this portable receipt.

## Mathematical and publication boundary

No finite replay is a general proof of type soundness, normalization, whole-domain equivalence, ordinal equality, BMS comparison or a PTO bound. Those claims remain at the paper status recorded in the [research index](README.md). There is no Lean build, new PDF rendering, independent mathematical review, commit or push in this integration. The previous notation implementations and Lean projects are untouched.
