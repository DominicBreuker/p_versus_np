# Approach: Circuit Complexity Lower Bounds

**Priority:** 90

**Status:** Active — Task 6 complete; Task 7 in progress;

**Relationship to the repository goal:** Main proof track. This approach directly targets `P ≠ NP` by formalizing the statement that sufficiently strong SAT circuit lower bounds would separate `P` from `NP`.

---

## Problem Statement

Prove that sufficiently strong Boolean circuit lower bounds for NP problems are enough to separate `P` from `NP`.
Specifically, formalize the argument that if an NP-complete problem such as SAT requires superpolynomial
circuit complexity, then `P ≠ NP`.

## Scope discipline

- Work in this folder must stay tied to the goal of settling P vs NP.
- Infrastructure results are useful only when they move this lower-bound route forward.
- Do not present Shannon-style counting progress as if it settled the SAT lower-bound problem itself.
- Keep the route barrier-aware.
- Counting lemmas and asymptotic bounds are worthwhile here only insofar as they clarify what this route can and cannot prove about explicit NP languages.

---

## Tasks

- [x] Task 1: Formalize Boolean circuit definitions (`BoolCircuit`, `Gate`, `CircuitNode`, `evalCircuit`)
- [x] Task 2: Define `IsPolynomial`, `inP`, and `inNP` in the circuit model
- [x] Task 3: Add sanity lemmas (`eval_const_true`, `eval_const_false`, `eval_var_zero`)
- [x] Task 4: Axiomatize Cook–Levin (`sat_is_np_complete`)
- [x] Task 5: Prove the conditional reduction from SAT circuit lower bounds to `P ≠ NP`
- [x] Task 6: Prove `circuit_count_lt_functions_at_n` — complete for all `n ≥ 4`
- [ ] Task 7: Complete `shannon_counting_argument` without overstating what it implies

---

## Key Axioms / Open Boundary

1. **`sat_is_np_complete`** — Cook–Levin theorem. Classically provable; formal proof is lengthy.
2. **`sat_has_superpoly_lower_bound`** — SAT requires superpolynomial-size circuits.
   **This is the unresolved step that would settle the P vs NP question in this route.**

The compiled `p_neq_np` theorem in `Proof.lean` is conditional on these assumptions.
Treat it as progress on the route, not as a solved proof of P vs NP.

---

## Library Code

Reusable definitions live in `lib/PVsNpLib/Utils.lean` and are imported via `import PVsNpLib`.
