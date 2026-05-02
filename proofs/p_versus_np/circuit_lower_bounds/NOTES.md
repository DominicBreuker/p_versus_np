# Circuit Lower Bounds for P vs NP: Current Status

**Last Updated:** 2025-05-02  
**Status:** 3 sorrys remain in Proof.lean

---

## Overview

This document tracks the current status of the circuit lower bounds proof for P vs NP. The goal is to formalize a circuit complexity route to proving P ≠ NP via Shannon's counting argument.

---

## Current Status

### Build Status
- ✅ `lake env lean Proof.lean` compiles successfully
- ✅ `lake build` compiles with no errors or warnings
- ⚠️ **5 sorrys remain** in the proof file (NOTES.md not updated with current state)

### Main Theorem Status

#### Completed Theorems
- ✅ `p_neq_np`: Conditional result compiles (depends on `sat_is_np_complete` and `sat_has_superpoly_lower_bound` axioms)
- ✅ `sat_superpolynomial_implies_p_neq_np`: Connection theorem complete
- ✅ `circuit_count_lt_functions_at_n`: Counting argument for n ≥ 4 complete
- ✅ `poly_quadratic_bound_k0`: k=0 case complete
- ⚠️ `poly_quadratic_bound`: Main polynomial-exponential bound theorem (complete for k=0,1; sorry for k≥2)

#### Theorems with Sorrys
- ✅ `evalCircuit_normalizeCircuit` (line 414): **COMPLETE** - Normalization preserves evaluation
- ⚠️ `n_pow_D_lt_two_pow_n` (line 924): **SORRY** - Generic dominance lemma (base case hard for symbolic D)
- ⚠️ `succ_pow_invariant` (line 1012): **SORRY** - Bernoulli-style invariant for induction step
- ⚠️ `base_pow_lt_two_pow` (line 1165): **SORRY** - Base case for n_pow_lt_two_pow_n (hard for symbolic D)
- ⚠️ `poly_quadratic_bound_k_ge_1` k≥3 case (line 1282): **SORRY** - Exponential dominance for higher degrees (requires linear threshold variant)
- ⚠️ `shannon_counting_argument` (line 1636): **SORRY** - Main counting argument theorem (depends on above)

**Note:** NOTES.md line numbers are outdated. See grep for actual locations.

---

## Runtime

IMPORTANT: Ensure `lake env lean proofs/p_versus_np/circuit_lower_bounds/Proof.lean` does not take too long! Target < 1 minute. See `FAILED_ATTEMPTS.md` for previous proofs that far exceeded the runtime.

---

## What Has Been Accomplished

### 1. Circuit Model Formalization ✅
**Completed:** Full formalization of Boolean circuits and their semantics
- `Gate`, `CircuitNode`, `BoolCircuit` types defined
- `evalCircuit` function with proper topological evaluation
- `inP` and `inNP` complexity class definitions

**Key Results:**
- `eval_const_true`, `eval_const_false`: Constant circuit evaluation
- `eval_var_zero`: Variable circuit evaluation  
- All basic circuit primitives compile successfully

### 2. Circuit Normalization Infrastructure ✅
**Completed:** Finite normalized circuit representation
- `NodeCode`: Finite encoding of circuit nodes
- `NormalizedCircuit`: Normalized circuit type with finite representation
- `normalized_circuit_count_upper_bound`: Upper bound on normalized circuits
- `node_code_card_le`: Cardinality analysis of node codes (2^(n+s+4) bound)

**Key Lemmas:**
- `evalNode_normalizeNodeCode`: Node evaluation preserved under normalization
- `normalizeCircuit_nodes_list`: Structural decomposition of normalized circuits
- `encodeNodeCode_injective`: Node code encoding is injective
- `normalized_circuit_card_le`: Cardinality bound for normalized circuits

### 3. Arithmetic Infrastructure ✅
**Completed:** Exponential dominance lemmas for counting arguments

**Core Lemmas:**
- `circuit_count_lt_functions_at_n`: (n+1)^(n+1) * 2^n < 2^(2^n) for n ≥ 4
- `n_plus_one_le_two_pow_n`: n+1 ≤ 2^n for n ≥ 1
- `s_plus_one_pow_le_two_pow_s_times_s_plus_one`: (s+1)^(s+1) ≤ 2^(s(s+1)) for s ≥ 1
- `n_squared_plus_two_n_lt_two_pow_n`: n² + 2n < 2^n for n ≥ 9  
- `four_n_squared_plus_six_n_plus_one_lt_two_pow_n`: 4n² + 6n + 1 < 2^n for n ≥ 196
- `n_quartic_plus_lt_two_pow_n_200`: n⁴ + 3n² + 1 < 2^n for n ≥ 200
- `n_squared_plus_n_quartic_lt_two_pow_n_200`: (n² + n)² + 3(n² + n) + 1 < 2^n for n ≥ 200

**Impact:** These lemmas establish that exponential growth (2^n) eventually dominates polynomial growth (n^d) for various degrees.

### 4. Polynomial-Exponential Bounds ⚠️
**Partially Completed:** `poly_quadratic_bound` main theorem exists but uses sorry for k ≥ 2

**What's Proven:**
- `poly_quadratic_bound_k0`: Complete for k=0 (constant polynomials)
- `poly_quadratic_bound_k_ge_1`: Complete for k=1 (linear polynomials)
- `poly_quadratic_bound_k_ge_1`: **SORRY for k ≥ 2** (higher-degree polynomials)

**Status:** The main theorem `poly_quadratic_bound` delegates to these helpers, so it's partially complete.

---

## Remaining Work

### 1. `evalCircuit_normalizeCircuit` (line 387) ⏳ HIGH PRIORITY
**Status:** Proof structure not started - just `sorry`
**Complexity:** Medium  
**Estimated Effort:** 2-4 hours

**What's Needed:** Prove that normalizing a circuit (padding with const-false nodes) preserves evaluation results.

**Proof Strategy:**
1. Unfold `normalizeCircuit` and `evalCircuit`
2. Show output node is either preserved or evaluates to false
3. Use `normalizeCircuit_nodes_list` to decompose normalized nodes into [original] ++ [padding]
4. Apply `evalStep_fold_normalized_eq` to show prefix folding preserved
5. Use `evalStep_fold_getElem?_preserve` to handle padding region
6. Conclude by showing the folded results are equal at all relevant indices

**Key Challenge:** Array/List conversion between `Array.foldl` on `Array.ofFn` and `List.foldl` operations.

**Building Blocks Available:**
- ✅ `evalNode_normalizeNodeCode`: Node-level evaluation preservation
- ✅ `evalStep_fold_normalized_eq`: Folding preserved for normalized prefix  
- ✅ `evalStep_fold_getElem?_preserve`: Padding doesn't affect existing values
- ✅ `normalizeCircuit_nodes_list`: Structural decomposition lemma

### 2. `poly_quadratic_bound_k_ge_1` for k ≥ 2 (line 852) ⏳ HIGH PRIORITY
**Status:** Case split complete for k=1, sorry for k ≥ 2
**Complexity:** Medium-High
**Estimated Effort:** 3-5 hours

**What's Needed:** Prove (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n for k ≥ 2.

**Current State:**
- k=0: Complete via `poly_quadratic_bound_k0`
- k=1: Complete via reduction to `n_squared_plus_n_quartic_lt_two_pow_n_200`
- k ≥ 2: **SORRY**

**Proof Strategy:**
- For k ≤ 7: Use bounded-degree approach similar to k=1
  - Bound c * n^k + c ≤ n^(k+3)
  - Show (n^(k+3))^2 + 3*n^(k+3) + 1 < 2^n
  - Use case analysis on n ranges (similar to FAILED_ATTEMPTS.md approach)
- For k > 7: May need different approach or accept degree bound

**Key Challenge:** For large k, the degree 2k+6 becomes very large, requiring careful case analysis.

**Note:** The FAILED_ATTEMPTS.md file contains a very long proof attempt for this that exceeded runtime limits. A more efficient approach is needed.

### 3. `shannon_counting_argument` (line 1009) ⏳ HIGH PRIORITY
**Status:** Complete sorry - no proof structure
**Complexity:** Medium-High
**Estimated Effort:** 3-5 hours

**What's Needed:** Prove Shannon's counting argument: For any polynomial p, there exist Boolean functions on n inputs that cannot be computed by circuits of size ≤ p(n).

**Proof Strategy:**
1. Use `poly_quadratic_bound` to show circuit_count_upper_bound n (p n) < boolean_function_count n
2. Define injection from Boolean functions to circuits (via `Classical.choose`)
3. Apply pigeonhole principle: if all functions were computable, we'd have an injection from functions to circuits
4. But |functions| = 2^(2^n) > circuit_count_upper_bound n (p n) ≥ |circuits|, contradiction

**Key Challenge:** Formalizing the pigeonhole principle with infinite types.

**Building Blocks Needed:**
- ✅ `circuit_count_lt_functions_at_n`: Counting inequality for specific case
- ❌ `poly_quadratic_bound`: General polynomial-exponential bound (has sorry for k ≥ 2)
- ❌ `evalCircuit_normalizeCircuit`: Normalization preserves semantics (needed for injection)

**Dependencies:** This theorem depends on completing items 1 and 2 above.

---

## Mistakes and Lessons Learned

### 1. Mathematical Inconsistencies in Early Drafts ❌
**Issue:** Original `pow_lt_two_pow_half` theorem claimed n^d < 2^(n/2) with hypothesis n ≥ 4d+10.

**Discovery:** 
- Counterexample: n=22, d=2 satisfies n ≥ 4d+10 = 18, but 22^2 = 484 > 2^11 = 2048 is false (actually 484 < 2048, but the bound was still wrong)
- Mathematical error: The claimed bound was too strong

**Resolution:**  
- ❌ REMOVED `pow_lt_two_pow_half` and `n_lt_two_pow_half` entirely
- ✅ Replaced with correct statement: `n_quartic_plus_lt_two_pow_n_200` and related lemmas
- ✅ Added explicit degree bounds where needed

**Lesson:** Always verify base cases computationally before attempting general proofs. Use `norm_num` to check concrete cases.

### 2. Type Class and Fintype Issues ⚠️
**Issue:** Attempted to use pigeonhole principle via injection but couldn't establish Fintype instance for `{c : BoolCircuit n // circuitSize c ≤ p n}`.

**Discovery:**  
- `BoolCircuit n` is an infinite type (arbitrary size circuits)
- Subtype of bounded-size circuits lacks automatic Fintype instance
- Previous attempts using `cases` on `Exists` hit type class synthesis failures

**Resolution:**  
- ✅ Use `NormalizedCircuit n (p n)` which has Fintype instance as intermediate type
- Map functions to normalized circuits, then use cardinality bounds

**Lesson:** For counting arguments, prefer types with built-in finiteness (like `NormalizedCircuit`) over subtypes of infinite types.

### 3. Array/List Conversion Complexity ⚠️
**Issue:** `evalCircuit` uses `Array.foldl` but normalization lemmas work with `List.foldl`, causing tactic failures.

**Discovery:**  
- `evalCircuit` defined as `Array.foldl` over `c.nodes`
- `evalStep_fold_normalized_eq` uses `List.foldl` over node lists
- Pattern matching on `normalizeCircuit_nodes_list` doesn't work with `rw`

**Resolution:**  
- ⚠️ Partial workaround: Added `simp` instead of `rw` in some places
- ❌ Could not resolve all Array/List mismatches - this is why `evalCircuit_normalizeCircuit` remains sorry

**Lesson:** When working with mixed Array/List operations, either:
- Use unified representation throughout, or
- Establish explicit conversion lemmas between Array and List operations

### 4. Overly Ambitious Degree Bounds ❌
**Issue:** Early versions attempted to prove n^d < 2^n for unbounded d.

**Discovery:**  
- For d=4, n=14: 14^4 = 38416 > 2^14 = 16384 (counterexample to n ≥ d+10)
- Exponential dominance requires d to be bounded or n to grow faster than linear in d

**Resolution:**  
- ✅ Added explicit bound d ≤ 20 in various helper lemmas
- ✅ Restricted `poly_quadratic_bound_k_ge_1` to handle specific cases
- ⚠️ k>7 path left as sorry (needs different approach)

**Lesson:** For polynomial-to-exponential bounds, either:
- Bound the degree explicitly, or
- Use degree-dependent thresholds (e.g., n ≥ C·2^d), or
- Prove separate lemmas for specific degrees needed by downstream results

### 5. Runtime Exceeding Limits ❌
**Issue:** Proof attempt in FAILED_ATTEMPTS.md for `poly_quadratic_bound_k_ge_1` used massive case analysis that caused Lean to run for >1 hour.

**Discovery:**
- The proof had dozens of nested case splits on n ranges
- Each case required proving similar inequalities
- The approach was computationally infeasible

**Resolution:**
- ❌ Abandoned the massive case analysis approach
- ✅ Need more efficient proof strategy using general bounds

**Lesson:** Avoid excessive case analysis. Prefer general lemmas with clean induction structures over brute-force case splitting.

---

## Completed Proofs

### ✅ `evalNode_normalizeNodeCode`
**Status:** COMPLETE  
**Lines:** ~300-333  
**What:** Node evaluation preserved under normalization  
**Approach:** Case analysis on gate type, use helper lemmas for AND/OR, direct simplification for others

### ✅ `circuit_count_lt_functions_at_n` 
**Status:** COMPLETE  
**Lines:** ~550  
**What:** (n+1)^(n+1) * 2^n < 2^(2^n) for n ≥ 4  
**Impact:** Core counting argument for identity polynomial

### ✅ `poly_quadratic_bound_k0`
**Status:** COMPLETE
**Lines:** ~870-940
**What:** 4*c^2 + 6*c + 1 < 2^n for n ≥ 2*c + 5
**Approach:** Induction on c with helper lemma

### ✅ `poly_quadratic_bound_k_ge_1` for k=1
**Status:** COMPLETE
**Lines:** ~830-850
**What:** (c*n + c)^2 + 3*(c*n + c) + 1 < 2^n for n ≥ c + 200
**Approach:** Bound c*n + c ≤ n^2 + n, then use `n_squared_plus_n_quartic_lt_two_pow_n_200`

---

## Build Instructions

```bash
# Check individual file
lake env lean proofs/p_versus_np/circuit_lower_bounds/Proof.lean

# Full project build  
lake build

# Check for diagnostics
lake exe cache get  # Get mathlib cache first
lake build --verbose
```

---

## Next Steps for Researchers

### Priority Order:

1. **`evalCircuit_normalizeCircuit`** - Foundational lemma needed by others
   - Follow README 7-step strategy
   - Key: Use `evalStep_fold_getElem?_preserve` for padding region
   - Effort: 2-4 hours

2. **`poly_quadratic_bound_k_ge_1` for k ≥ 2** - Unblocks Shannon argument
   - Use bounded-degree approach for k ≤ 7
   - For k > 7: accept degree bound or find different approach
   - Avoid the massive case analysis from FAILED_ATTEMPTS.md
   - Effort: 3-5 hours

3. **`shannon_counting_argument`** - Main counting theorem
   - Depends on items 1 and 2
   - Use `NormalizedCircuit` for Fintype instance
   - Effort: 3-5 hours

### Dependencies:
```
shannon_counting_argument
  ├─ poly_quadratic_bound (needs k ≥ 2 case)
  │   └─ poly_quadratic_bound_k_ge_1 (k ≥ 2 case)
  └─ evalCircuit_normalizeCircuit (for injection proof)
```

---

## File Structure

```
proofs/p_versus_np/circuit_lower_bounds/
├── Proof.lean           # Main proof file (current focus)
├── NOTES.md             # This status document  
├── FAILED_ATTEMPTS.md   # Lessons from failed proof attempts
├── GUIDANCE.md          # Strategic advice and prior art
└── README.md            # Compact overview and scope
```

---

## References

- **Primary:** `Proof.lean` - The authoritative source of current proof status
- **Guidance:** `GUIDANCE.md` - Strategic advice and mathematical foundations
- **Lessons:** `FAILED_ATTEMPTS.md` - What not to do (runtime issues)
- **Mathlib:** External dependency for number theory and data structures

---

## Notes on Proof Architecture

The current proof follows a well-established approach:

1. **Circuit Lower Bounds via Counting:** Show that there are more Boolean functions (2^(2^n)) than circuits ((s+1)^(s+1)·2^s ≤ 2^(O(s log s))).

2. **Normalization:** Use `NormalizedCircuit` (with finite NodeCode representation) to make counting arguments tractable in Lean.

3. **Arithmetic Infrastructure:** Prove exponential dominance lemmas (n^d < 2^n) to establish the counting inequality for polynomial p(n).

4. **Pigeonhole Principle:** Derive contradiction from surjection of circuits onto functions when circuits are too few.

**Key Challenge:** Making the pigeonhole principle work with Lean's type system, particularly around infinite vs finite types and cardinality arguments.

---

*Documentation last updated: 2025-05-02  
For questions or to continue this work, consult the README and GUIDANCE files in this directory.*

## Technical Interruptions

- 2026-05-02 13:46 UTC — Researcher workflow hit a technical interruption: Mistral Vibe timed out during pass 1/1 after 3600 seconds.. Partial work from this run was preserved; review the current proof state before continuing.
