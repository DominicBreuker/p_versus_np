# Approach: Circuit Complexity Lower Bounds

**Priority:** 90

**Status:** Active — this is the repository's primary route toward a Lean proof of `P ≠ NP`, but the current formal result is still only conditional and the decisive lower-bound work remains open

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
- Keep the route barrier-aware: counting lemmas and asymptotic bounds are worthwhile here only insofar as they clarify what this route can and cannot prove about explicit NP languages.

---

## Tasks

- [x] Task 1: Formalize Boolean circuit definitions (`BoolCircuit`, `Gate`, `CircuitNode`, `evalCircuit`)
- [x] Task 2: Define `IsPolynomial`, `inP`, and `inNP` in the circuit model
- [x] Task 3: Add sanity lemmas (`eval_const_true`, `eval_const_false`, `eval_var_zero`)
- [x] Task 4: Axiomatize Cook–Levin (`sat_is_np_complete`)
- [x] Task 5: Prove the conditional reduction from SAT circuit lower bounds to `P ≠ NP`
- [ ] Task 6: Prove `circuit_count_lt_functions_at_n` — remove the arithmetic `sorry`
- [ ] Task 7: Complete `shannon_counting_argument` without overstating what it implies

---

## Key Axioms / Open Boundary

1. **`sat_is_np_complete`** — Cook–Levin theorem. Classically provable; formal proof is lengthy.
2. **`sat_has_superpoly_lower_bound`** — SAT requires superpolynomial-size circuits.
   **This is the unresolved step that would settle the P vs NP question in this route.**

The compiled `p_neq_np` theorem in `Proof.lean` is conditional on these assumptions.
Treat it as progress on the route, not as a solved proof of P vs NP.

---

## Immediate Next Steps

### Task 6 — Prove `circuit_count_lt_functions_at_n` for `n ≥ 9`

Goal: `(n + 1)^(n + 1) * 2^n < 2^(2^n)` for `n ≥ 9`.

Recommended route:
- Step A: Prove `n + 1 ≤ 2^n` for `n ≥ 1`.
- Step B: Lift that bound to `(n + 1)^(n + 1) ≤ 2^(n * (n + 1))`.
- Step C: Prove `n^2 + 2*n < 2^n` for `n ≥ 9`.
- Step D: Combine the exponent bounds to conclude the target inequality.
- Prefer short standalone arithmetic lemmas over a single monolithic proof so the argument can be reused in Task 7.

### Task 7 — Complete `shannon_counting_argument`

Once Task 6 is done, formalize the usual counting argument carefully:
1. Bound a general polynomial `p n` by a simpler growth term for sufficiently large `n`.
2. Show `circuit_count_upper_bound n (p n) < boolean_function_count n` eventually.
3. Use pigeonhole reasoning to extract a Boolean function that escapes every circuit family of size `≤ p n`.

Keep the final statement honest: Shannon counting yields existential lower bounds for *some* Boolean functions, not a SAT-specific lower bound.

## Guidance for the next researcher pass

- First finish the arithmetic helper chain for Task 6; that is the cleanest bottleneck in the whole repository.
- Once Task 7 compiles, stop and reassess before adding any stronger claim: the next missing ingredient would still be an explicit SAT lower bound, not more existential counting.
- Do not branch from this folder into quantum, proof-complexity, or GCT explorations unless the Project Leader creates a separate justified route.

---

## Library Code

Reusable definitions live in `lib/PVsNpLib/Utils.lean` and are imported via `import PVsNpLib`.
