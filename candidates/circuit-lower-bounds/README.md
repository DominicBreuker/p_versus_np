# Idea: Circuit Complexity Lower Bounds

**Priority:** High

**Status:** Active

---

## Problem Statement

Prove that Boolean circuit complexity lower bounds for NP problems are sufficient to separate P from NP.
Specifically, formalize the argument that if any NP-complete problem (e.g., SAT) requires superpolynomial
circuit complexity, then P ≠ NP.

**Approach:**
1. Define Boolean circuits and circuit complexity formally in Lean4.
2. Define the complexity classes P and NP in terms of circuit families.
3. Prove (or assume as axiom) that SAT is NP-complete.
4. Develop lower bound lemmas showing exponential circuit complexity for some NP instance.
5. Conclude P ≠ NP.

---

## Tasks

- [ ] Task 1: Formalize Boolean circuit definitions (gates, wires, circuit size)
- [ ] Task 2: Define polynomial-size circuit families (P/poly)
- [ ] Task 3: Define NP via nondeterministic computation or witnesses
- [ ] Task 4: State Cook–Levin theorem (SAT is NP-complete) — can be axiomatized
- [ ] Task 5: Prove a superpolynomial lower bound for some Boolean function
- [ ] Task 6: Connect lower bound to P ≠ NP separation

---

## Hints

- Start with small lemmas. Formalizing circuits in Lean4 requires careful handling of induction on circuit depth.
- The Razborov–Smolensky method (algebraization) is one route to lower bounds.
- Shannon counting argument gives an *existence* proof that most Boolean functions need exponential circuits — try formalizing this first.
- The `lib/utils.lean` file contains shared definitions; use and extend them as needed.

---

## Library Code

Reusable definitions should live in `lib/utils.lean`. Factor out:
- `BoolCircuit` type definition
- `circuitSize` function
- Any combinatorics lemmas used repeatedly
