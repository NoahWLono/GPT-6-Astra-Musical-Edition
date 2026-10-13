# GPT-6 Astra Musical Edition

A public workspace for mathematical research in music theory.

## Status

Initial research is underway on the three problems below. The goal is a novel, proven theorem for each project, with a checked Lean 4 proof and a LaTeX/PDF write-up. No completed results, proved conjectures, or checked Lean 4 proofs are included in this repository yet.

## Research queue

1. **Six-note homometric chord classification across all n.** Investigate the six-element case of [Erickson and Jones, Problem 5.2](https://arxiv.org/html/2412.08997v4#S5), beginning with the precise scope and existing results.
2. **Pyle's omnibus Conjecture 1 for three- through six-note sonorities.** Investigate the conjecture in [Pyle's paper](https://musmat.org/journal/v9/02-Pyle.pdf), with definitions and hypotheses fixed before theorem claims.
3. **Algebraic tuning optimality.** Develop a precise optimization problem informed by [Algebraic tunings](https://people.maths.bris.ac.uk/~macpd/music/Algebraic_tunings.pdf). This research direction still requires a precise problem formulation; no particular optimality theorem is claimed.

Novelty will be assessed against the literature before a result is presented as new. Proof discovery, formal verification, and exposition are separate stages.

## Research workflow

Each problem will receive a numbered folder under `problems/` (for example, `problems/001-short-title/`) containing:

- A precise problem statement, definitions, assumptions, and source references
- Research notes and reproducible computations where useful
- Lean 4 formalizations, with proof-checking status and toolchain recorded
- LaTeX source and a corresponding PDF write-up when ready
- Sheet music or musical notation where it helps explain the result

Exploratory evidence will be distinguished from proofs. A result will be described as formally verified only after its Lean 4 proof has been checked.

## Planned organization

Numbered problem folders and proof/write-up files will be added as research deliverables are prepared.
