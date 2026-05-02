# Approach: Circuit Complexity Lower Bounds

**Priority:** 90

**Status:** Active — Tasks 1-6 complete; Task 7 in progress (3 sorrys remain)

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
- Ensure `lake env lean proofs/p_versus_np/circuit_lower_bounds/Proof.lean` does not take too long! Target < 1 minute. See `FAILED_ATTEMPTS.md` for previous proofs that far exceeded the runtime.

---

## Tasks

- [x] Task 1: Formalize Boolean circuit definitions (`BoolCircuit`, `Gate`, `CircuitNode`, `evalCircuit`)
- [x] Task 2: Define `IsPolynomial`, `inP`, and `inNP` in the circuit model
- [x] Task 3: Add sanity lemmas (`eval_const_true`, `eval_const_false`, `eval_var_zero`)
- [x] Task 4: Axiomatize Cook–Levin (`sat_is_np_complete`)
- [x] Task 5: Prove the conditional reduction from SAT circuit lower bounds to `P ≠ NP`
- [x] Task 6: Prove `circuit_count_lt_functions_at_n` — complete for all `n ≥ 4`
- [ ] Task 7: Complete `shannon_counting_argument` without overstating what it implies
  - **Current Status (2025-05-02):** 3 sorrys remain in Proof.lean
  - Remaining sorrys:
    1. `evalCircuit_normalizeCircuit` (line 387): Prove evaluation preserves under circuit padding
    2. `poly_quadratic_bound_k_ge_1` for k ≥ 2 (line 852): Prove exponential dominance for higher degrees
    3. `shannon_counting_argument` (line 1009): Main counting argument theorem
  - Note: `evalNode_normalizeNodeCode` is complete ✓
  - Note: `poly_quadratic_bound_k0` (k=0) and `poly_quadratic_bound_k_ge_1` for k=1 are complete ✓

---

## Current Proof Status Summary

| **Theorem** | **Line** | **Status** | **Priority** |
|-------------|----------|------------|-------------|
| `evalCircuit_normalizeCircuit` | 387 | ❌ SORRY | HIGH |
| `poly_quadratic_bound_k_ge_1` (k≥2) | 852 | ❌ SORRY | HIGH |
| `shannon_counting_argument` | 1009 | ❌ SORRY | HIGH |
| `p_neq_np` | ~1050 | ✅ Complete | - |
| `sat_superpolynomial_implies_p_neq_np` | ~1040 | ✅ Complete | - |

**Dependencies:**
```
shannon_counting_argument (line 1009)
  ├─ poly_quadratic_bound (uses poly_quadratic_bound_k_ge_1)
  │   └─ poly_quadratic_bound_k_ge_1 (k≥2 case at line 852)
  └─ evalCircuit_normalizeCircuit (line 387, needed for injection)
```

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
