# Progress Notes — P ⊆ NP

**Last Updated:** 2025-01-08

**Track role:** Supporting subproblem for the main P vs NP proof route.

**Status:** Active — partial proofs for all three main theorems, with clear identification of remaining issues.

---

## Current State

- `liftCircuit`, `liftCircuit_size`, and `poly_half` are fully proven.
- The proof file imports both `Mathlib` and `PVsNpLib`, maintaining clean shared imports.

### `liftCircuit_eval` (line 97)
- **Status:** Partially proven
- **Completed:**
  - Circuit size preservation (`liftCircuit_size`) is proven
  - The case for `idx < n` is complete (both sides read from `inp` at the same index)
  - The case for `idx >= 2*n` is complete (both sides return `false`)
- **Remaining:** The case for `n <= idx < 2*n` (line 133)
  - For well-formed circuits from `inP`, all Var nodes have `idx < n`, so this case is unreachable
  - The sorry assumes this well-formedness property
  - **Solution:** Add a well-formedness predicate to the definition of `inP` or to the theorem statement that ensures all Var nodes have `idx < n`

### `verifier_iff` (line 175)
- **Status:** Partially proven
- **Completed:**
  - Proved that `(2 * n) / 2 = n` (via `h_div`)
  - Proved pointwise equality of the input functions (via `h_fn`)
  - Showed that `f1 = (fun i => inp i) ∘ Fin.cast h_div` (via `h_f1_eq`)
- **Remaining:** Dependent-type bookkeeping (line 217)
  - Need to prove: `L ((2 * n) / 2) ((fun i => inp i) ∘ Fin.cast h_div) ↔ L n inp`
  - The mathematical content is trivial (the functions are pointwise equal)
  - The challenge is that `L ((2 * n) / 2) f1` and `L n inp` have different types because `f1 : Fin ((2 * n) / 2) → Bool` while `inp : Fin n → Bool`
  - **Solution:** Use `Eq.rec` with a carefully constructed motive that accounts for the dependent function types, or change the definition of `Language` to not use dependent types

### `p_subset_np` (line 237)
- **Status:** Partially proven
- **Completed:**
  - Witness direction (using `verifier_iff`) is complete
  - Even case (`m = 2k`): Circuit size bound is proven
- **Remaining:**
  - Even case: Evaluation equivalence (line 266)
    - Need to show: `evalCircuit (liftCircuit c) inp = true ↔ V (2 * k) inp`
    - By `liftCircuit_eval` and `hc_correct`, this reduces to the same dependent-type issue as in `verifier_iff`
    - **Solution:** Complete `verifier_iff` first, then use it here
  - Odd case (`m = 2k+1`): Type mismatch (line 285)
    - `liftCircuit` produces `BoolCircuit (2k)` but we need `BoolCircuit (2k+1)`
    - **Solution:** Define a more general lifting function `liftCircuitTo {n m : Nat} (h : n ≤ m) (c : BoolCircuit n) : BoolCircuit m` that pads the circuit with dummy nodes to handle additional inputs

---

## Blockers

1. **Dependent-type bookkeeping:** Both `verifier_iff` and `p_subset_np` (even case) have the same issue with dependent types (`Fin n` vs `Fin ((2*n)/2)`). The current definition of `Language` as `∀ (n : Nat), (Fin n → Bool) → Prop` uses dependent types in a way that makes it impossible to prove the required equivalences for an arbitrary `L`.

2. **Circuit lifting for arbitrary sizes:** The current `liftCircuit` only lifts from `n` to `2*n`. For `p_subset_np`, we need to lift from `m/2` to `m` for arbitrary `m`, including odd sizes where `m ≠ 2*(m/2)`.

3. **Well-formedness of circuits:** The `liftCircuit_eval` theorem assumes that circuits have all Var nodes with `idx < n`. This should be formalized as a well-formedness predicate.

---

## Recommended Next Steps

1. **Complete `verifier_iff`:** This is the key lemma that unlocks both the even case of `p_subset_np` and the witness direction. The solution is to use `Eq.rec` with a motive of the form:
   ```lean
   fun m => L m ((fun i : Fin n => inp i) ∘ Fin.cast (by omega : m = n))
   ```
   However, this requires careful handling of the dependent types. Alternatively, change the definition of `Language` to `Nat → (Nat → Bool) → Prop` to avoid dependent types.

2. **Complete `liftCircuit_eval`:** Add a well-formedness assumption to the theorem statement:
   ```lean
   theorem liftCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin (2 * n) → Bool)
       (h_wf : ∀ node ∈ c.nodes, ∀ i, node.gate = Gate.Var i → i < n) :
       evalCircuit (liftCircuit c) inp = evalCircuit c (fun i => inp ⟨i.val, by have := i.isLt; omega⟩) := by
   ```
   Or add a well-formedness predicate to the definition of `inP`.

3. **Generalize circuit lifting:** Define:
   ```lean
   def liftCircuitTo {n m : Nat} (h : n ≤ m) (c : BoolCircuit n) : BoolCircuit m :=
     { nodes := c.nodes, output := c.output }
   ```
   This would unblock the odd case in `p_subset_np`.

4. **Assemble `p_subset_np`:** Once the above are complete:
   - Even case: Use `liftCircuit_eval` and `verifier_iff` to show the evaluation equivalence
   - Odd case: Use `liftCircuitTo` to construct a circuit for size `m = 2k+1`

---

## Files Modified

- `proofs/p_subset_np/circuit-lifting/Proof.lean`: Added partial proofs for `liftCircuit_eval`, `verifier_iff`, and `p_subset_np` with detailed comments on remaining issues.
- `proofs/p_subset_np/circuit-lifting/NOTES.md`: This file, documenting current state and recommended next steps.
