# DQDN and the unproved PTO upper bound · [中文版](upper-bound-open.zh-CN.md)

The global lower-bound argument is not a proof of equality with PTO(Zω). This note records the two outstanding internalization obligations; it is not used as a premise of the lower bound.

## A sufficient route

If, for each fixed k, some finite-order full-comprehension arithmetic Z_f(k) proves well-ordering of the **whole** P_k standard domain, then |P_k|<PTO(Zω). The strict inequality follows by adjoining a greatest element in the same theory. Taking the supremum over k gives the reverse inequality. Combined with the existing lower bound, this would establish the global equality.

The step cannot be replaced by separately proving termination of each individual program in the generator. Nor is it necessary to define a theory's own PTO internally just to adjoin one maximum.

## Controlling object orders

The generator bounds kind-tree height, not just the number of written quantifiers. There are finitely many kind shapes at fixed height. A base-kind semantic value is a reducibility candidate, a set of program codes; arrow kinds use graphs of functions between the relevant candidate spaces. Each fixed finite kind bound therefore suggests only finitely many powerset levels. Finite environments can be encoded by same-order finite tuples, without a free universe containing every kind height.

Strong normalization already quantifies over program sequences and is a second-order condition. Forming candidates and interpreting higher kinds needs additional finite orders. No exact Z_(k+2) or Z_(k+3) bound has been checked.

## Outstanding internalizations

First, one needs a **uniform** interpretation of every finite type derivation at the fixed kind level, with arbitrary legal assignments. An interpretation formula for each externally fixed type is insufficient for the whole generator. One proposed construction uses finite syntax-depth approximations and uniqueness, but the required comprehension levels have not been fully accounted for.

Second, one needs an internal proof from source well-foundedness to standard-column well-ordering. This may use well-founded finite multiset extensions instead of external set-theoretic ordinal ranks. The common-root prefix argument must also be internalized, including effective standardness and selecting finite descent paths. Quoting an external ZFC rank assignment does not discharge this task.

Accordingly, both the global exact PTO equality and any claimed least axiomatic upper bound remain open. The same caution applies to claiming TOP[2]=PTO(Z₂). Neither equality is supplied by finite tests or by a short program for large lower bounds.
