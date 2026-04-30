# Progress Notes — P ⊆ NP

**Last Updated:** 2026-04-30

**Track role:** Supporting subproblem for the main P vs NP proof route.

**Status:** Active — made progress on `liftCircuit_eval` by adding well-formedness predicate.

---

## Current State

- `liftCircuit`, `liftCircuit_size`, and `poly_half` are fully proven.
- The proof file imports both `Mathlib` and `PVsNpLib`, maintaining clean shared imports.

### `liftCircuit_eval` (line 101)
- **Status:** Partially proven - added well-formedness predicate
- **Completed:**
  - Added `IsWellFormed` predicate: `∀ node ∈ c.nodes, ∀ i, node.gate = Gate.Var i → i < n`
  - Modified theorem signature to take `h_wf : IsWellFormed c` as an argument
  - Proved helper lemma `h_nodes`: for all nodes in `c.nodes`, `evalNode inp acc node = evalNode (fun i => inp ⟨i.val, _⟩) acc node`
  - Proved helper lemma `h_step`: for all `acc` and `node ∈ c.nodes`, the push operations are equal
- **Remaining:**
  - Prove the foldl equality using `h_step`
  - The issue is that `Array.foldl_congr` doesn't provide membership proofs for nodes
  - Need to prove that the two foldl computations are equal when the step functions are equal on the array elements

### `verifier_iff` (line 172)
- **Status:** Partially proven - no progress from previous state
- **Completed:**
  - Proved that `(2 * n) / 2 = n` (via `h_div`)
  - Proved pointwise equality of the input functions (via `h_fn`)
  - Showed that `f1 = (fun i => inp i) ∘ Fin.cast h_div` (via `h_f1_eq`)
- **Remaining:** Dependent-type bookkeeping
  - Need to prove: `L ((2 * n) / 2) ((fun i => inp i) ∘ Fin.cast h_div) ↔ L n inp`
  - The mathematical content is trivial (the functions are pointwise equal)
  - The challenge is that `L ((2 * n) / 2) f1` and `L n inp` have different types because `f1 : Fin ((2 * n) / 2) → Bool` while `inp : Fin n → Bool`
  - **Solution:** Use `Eq.rec` with a carefully constructed motive that accounts for the dependent function types, or change the definition of `Language` to not use dependent types

### `p_subset_np` (line 271)
- **Status:** Partially proven - updated to use well-formedness
- **Completed:**
  - Witness direction (using `verifier_iff`) is structurally complete (but `verifier_iff` has sorry)
  - Even case (`m = 2k`): Circuit size bound is proven
  - Added well-formedness assumption for circuits from `inP`
- **Remaining:**
  - Even case: Evaluation equivalence
    - Need to show: `evalCircuit (liftCircuit c) inp = true ↔ V (2 * k) inp`
    - Now uses `liftCircuit_eval c inp h_wf` where `h_wf` is derived from the assumption that circuits from `inP` are well-formed
    - Still blocked by `liftCircuit_eval` and `verifier_iff`
  - Odd case (`m = 2k+1`): Type mismatch
    - `liftCircuit` produces `BoolCircuit (2k)` but we need `BoolCircuit (2k+1)`
    - **Solution:** Define a more general lifting function `liftCircuitTo {n m : Nat} (h : n ≤ m) (c : BoolCircuit n) : BoolCircuit m`

---

## Blockers

1. **Dependent-type bookkeeping:** `verifier_iff` has the same issue with dependent types (`Fin n` vs `Fin ((2*n)/2)`). The current definition of `Language` as `∀ (n : Nat), (Fin n → Bool) → Prop` uses dependent types in a way that makes it impossible to prove the required equivalences for an arbitrary `L`.

2. **Circuit lifting for arbitrary sizes:** The current `liftCircuit` only lifts from `n` to `2*n`. For `p_subset_np`, we need to lift from `m/2` to `m` for arbitrary `m`, including odd sizes.

3. **Foldl equality for well-formed circuits:** The `liftCircuit_eval` proof needs to show that two foldl computations are equal when the step functions are equal on the array elements. This requires a lemma that `Array.foldl` respects pointwise equality of the step function on the array elements.

---

## Recommended Next Steps

1. **Complete `liftCircuit_eval`:**
   - Prove the foldl equality by showing that for all nodes in `c.nodes`, the step functions are equal
   - This can be done by proving a lemma: if `∀ node ∈ arr, f acc node = g acc node`, then `arr.foldl f init = arr.foldl g init`
   - Or use `Array.foldl_eq_foldl` with a proof that the functions are equal on the array

2. **Complete `verifier_iff`:** This is the key lemma that unlocks both the even case of `p_subset_np` and the witness direction. The solution is to use `Eq.rec` with a motive of the form:
   ```lean
   fun m => L m ((fun i : Fin n => inp i) ∘ Fin.cast (by omega : m = n))
   ```
   However, this requires careful handling of the dependent types. Alternatively, change the definition of `Language` to `Nat → (Nat → Bool) → Prop` to avoid dependent types.

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

- `proofs/p_subset_np/circuit-lifting/Proof.lean`:
  - Added `IsWellFormed` predicate for circuits
  - Modified `liftCircuit_eval` to take well-formedness assumption
  - Proved helper lemmas `h_nodes` and `h_step` for `liftCircuit_eval`
  - Updated `p_subset_np` to use well-formedness assumption
- `proofs/p_subset_np/circuit-lifting/NOTES.md`: This file, updated to reflect current state and recommended next steps.

## Technical Interruptions

- 2026-04-30 01:19 UTC — Researcher workflow hit a technical interruption: Mistral Vibe timed out during pass 2/2 after 1800 seconds.. Partial work from this run was preserved; review the current proof state before continuing.
