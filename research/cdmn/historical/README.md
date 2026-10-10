# Historical CDMN evidence · [中文版](README.zh-CN.md)

These files preserve bounded research observations, not a current release-test receipt, mathematical proof, or claim that every original script and dependency is included. Unknowns, budget exits, incomplete replay and scope truncations remain unexamined cases. Counts are visits/checks, not necessarily distinct expressions.

## Earlier deep-zero experiments

The four original receipts use earlier deep-zero semantics. The current prefix-zero rule has the same finite reachable domain by the paper simulation lemma, but individual [0] steps and fixed-index macros differ. Do not reuse their exact paths unchanged.

| Receipt | Scope | Limits |
| --- | --- | --- |
| [Final-spine replicas](dilated-replica-results.json) | 61,731 steps; 7,622,655 positions | No hit; 101 size, 763 engine stops |
| [Internal replicas](interior-replica-results.json) | 31,456 steps; 47,295,896 positions | No hit; 291 size, 291 engine stops; 3,400 scope truncations |
| [Periodic families](periodic-flat-results.json) | 99,304 visits; 107,183 families | No first family transition; no budget stop |
| [Old dilation macros](dilation-results.json) | 17,139 cases; 49,484 replay steps | Old delta-based macro, not the current literal [0] formula |

The [dilation note](../dilation.md) and package tests distinguish the revised macro. Equal reachability does not imply equal macro length bounds.

## Prefix-zero BMS equality checks

Original source label: output/cdmn-s2-bms-20261009. The [full paper](../papers/s2-equals-bms.md) supplies the universal argument independently of sampling.

- [Standard sibling code](flat-sibling-code-results.json): 9,000 states; 27,000 positive and 9,000 zero checks. Of 10,079 endpoint corrections, 7,584 exceeded the preparation replay allowance and were checked only for shape, not complete paths. There were also 630 width stops.
- [Raw invariant checks](raw-flat-sibling-code-results.json): 2,400 raw graphs; 86 of 390 corrections likewise stopped early. Raw legality is not global standardness.
- [Independent transport](shadow-transport-results.json): 3,000 states, 8,742 positive steps, 408,289 parent and 408,289 depth equations, plus two-row regression; 308 width stops remained outside the completed checks.

## Four-hour prefix-zero research

The [original aggregate](four-hour-results.json) came from output/cdmn-four-hour-bounds-20261010/VERIFICATION.json. It includes invariant tests, source simulations, searches and unclaimed extensions. Its final statement about no repository edits describes that historical run, not this packaging update.

| Batch | Finite scope | Limits |
| --- | --- | --- |
| TBMS to T | 1,498 source edges; 18,126 native steps | 1 resource unknown, 1 size skip |
| Uniform-family identities | 900 identities | No unknown or skip |
| Mixed-port driver | 1,560 raw states; 4,801 checks; 576 final-reader formulas | 3 size skips; raw inputs are not asserted standard |
| Mixed-port independent Python | 141 complete paths; 222 exact edges | No skip |
| Adjacent-reader independent Python | 104 complete paths; 178 exact edges | No skip |
| A/C2 closed-replica search | 30,335 steps; 9,537,360 candidate visits | No hit; 973 size stops, 39 unknowns, 13,288 scope truncations |

Experiments beyond R∞ are explicitly labeled unclaimed; they do not extend the proved frontier.

## Adjacent-reader BTBMS comparison

The [original receipt](adjacent-btbms-results.json), originally ADJACENT-BTBMS-VERIFICATION.json, records 33 first-layer and 144 positive second-layer identities, 16 zero simulations, 1,802 deeper source-edge simulations and 32,135 native target replays. It retains 1 source unknown and 351 size/path skips. Successful finite edges do not prove complete closure.

The original BTBMS core SHA256 was d058d391a4016e9861258204b0ffce8aa0860541e6d3ee2af74f1f671c15d8c0. The prefix-zero CDMN research core SHA256 was 306e8201f0a71b23a6ce062a21101e91051bf00b033ad0b7238c98bb57d8e4f1. These identify research inputs, not every current frontend artifact.

## Current package replay

Run python -B tests/cdmn.py from the repository root for the maintained suite. Its [release receipt](../../../tools/cdmn-validation.json) is separate from historical statistics. Original tools named inside the papers were not all ported and are not promised as runnable package commands. Universal claims retain their stated paper-proof status.
