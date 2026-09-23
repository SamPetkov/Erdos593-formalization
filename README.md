# Erdős 593: Lean classification and finite extensions

The existing root-level Lean source formalizes the finite classification of
obligatory triple systems. Its principal public endpoints are

```lean
Erdos593.TripleSystem.isObligatory_iff_isolatedReduction_intrinsic
Erdos593.TripleSystem.isObligatory_iff_constructible_isolatedReduction
```

Their statements are respectively

```lean
F.IsObligatory ↔ F.isolatedReduction.Intrinsic
F.IsObligatory ↔ Constructible F.isolatedReduction
```

## Independent development and attribution

This repository accompanies Samuil Petkov's independently developed proof and
formalization. Eric Li's separate classification proof is cited in the manuscript.
The chronology of public posting and the mathematical similarities between the
proofs are not treated here as evidence of informational dependence.
See `PROVENANCE.md` for the distinction between the author's development account
and what kernel verification establishes. No private correspondence is published.

Classical inputs retain their attribution. In particular, the manuscript invokes
the Erdős--Hajnal high-odd-girth theorem; the Lean implementation retains its
explicit shift-graph realization rather than adding a project axiom.

## Source and synchronization status

The root-level proof is the earlier classification snapshot. The later accepted
private standalone is larger and is NOT yet mirrored here by this change.
The matched `standalone-release/` files lock one accepted checkpoint and one
consolidated extension bundle. They are synchronization controls, not a claim
that matching proof payloads or new compiler verification already exist.

Running the reviewed local release command creates matching `standalone/`
subtrees in fresh private/public branches. It verifies the proof bytes, pins,
publication allowlist and Git subtree equality. The extended candidate cannot
be mirrored without passing its full-source compilation, ordered axiom audit
and full-type check in that run. No main branch is merged automatically.

The finite decomposition, grading, realization, counting and stability candidates
are not all canonically accepted. Nor does their compilation alone establish
formal coverage of every retained statement in the expanded manuscript.

## Existing build

```sh
lake build
python scripts/generate_self_contained.py --check
lake env lean Erdos593.lean
lake env lean Erdos593SelfContained.lean
```

The project is pinned to Lean/mathlib4.32. The root-level `Challenge.lean`,
`Solution.lean` and comparator adapter are preserved unchanged. A new standalone
release does not silently relabel those older adapter files as synchronized.

## Trust boundary

Formal verification applies to the exact source, theorem statements and
transitive dependencies actually checked. The permitted foundations are the
standard `propext`, `Classical.choice` and `Quot.sound`, or subsets. Source scans,
finite tests, matching manifests and successful preparation are not substitutes
for kernel checking. Verification does not establish historical priority or
informational independence.
