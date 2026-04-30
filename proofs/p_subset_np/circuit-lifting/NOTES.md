# Progress Notes — P ⊆ NP

**Last Updated:** 2025-01-14

**Track role:** Supporting subproblem for the main P vs NP proof route.

**Status:** Active — file compiles with 2 sorries (both for well-formedness), `verifier_iff` now proven, even and odd cases in `p_subset_np` complete except for well-formedness

---

## Current State

- `liftCircuit`, `liftCircuit_size`, `liftCircuitTo`, `liftCircuitTo_size`, `liftCircuit_eval`, `liftCircuitTo_eval`, and `poly_half` are fully proven.
- `IsWellFormed` predicate added to ensure circuits have valid Var node indices.
- `verifier_iff` is now **fully proven** (no sorry).
- The proof file imports both `Mathlib` and `PVsNpLib`, maintaining clean shared imports.
- File compiles successfully with only 2 sorries (both for well-formedness in `p_subset_np`).

### `liftCircuit_eval` (line ~153)
- **Status:** Fully proven (with `IsWellFormed` assumption)
- **Completed:**
  - Added `IsWellFormed` predicate: `∀ i < c.nodes.size, ∀ j, c.nodes[i]!.gate = Gate.Var j → j < n`
  - Modified theorem signature to take `h_wf : IsWellFormed c` as an argument
  - Proved helper lemma `h_nodes`: for all `i < c.nodes.size` and all `acc`, `evalNode inp acc c.nodes[i]! = evalNode (fun i => inp ⟨i.val, _⟩) acc c.nodes[i]!`
  - Proved the foldl equality using `Array.foldl_toList` and `List.foldl_ext`
- **Note:** The `IsWellFormed` assumption is necessary because when `n ≤ idx < 2*n`, the LHS evaluates to `inp ⟨idx, h⟩` while the RHS evaluates to `false`. So the theorem is NOT true without the well-formedness assumption.

### `liftCircuitTo_eval` (line ~106)
- **Status:** Fully proven
- **Completed:**
  - Added theorem with identical proof to `liftCircuit_eval`
  - Supports lifting circuits to arbitrary larger sizes (needed for odd case in `p_subset_np`)
  - Also requires `IsWellFormed` assumption for the same reason as `liftCircuit_eval`

### `verifier_iff` (line ~264)
- **Status:** **Fully proven** (no sorry)
- **Solution:** Used nested `Eq.rec` with carefully chosen motives to handle the dependent-type bookkeeping.
- **Key insight:** For `i : Fin ((2*n)/2)`, we have `i.val < n`, so the combined function at `i` equals `inp ⟨i.val, _⟩`.
- **Proof structure:**
  - Showed that the combined function equals `inp ∘ Fin.cast h_div` where `h_div : (2*n)/2 = n`
  - Used `Eq.rec` to transport `L` along `h_div` with a motive that handles the function transport
  - Proved that `Fin.cast h_div i = ⟨i.val, _⟩` for all `i : Fin ((2*n)/2)`

### `p_subset_np` (line ~359)
- **Status:** Partially proven - structure in place, uses `liftCircuit` and `liftCircuitTo`
- **Completed:**
  - Verifier definition: `V(m)(inp) = L(m/2)(inp restricted to first m/2 bits)`
  - Polynomial bound: `p(m/2) + 1` with proof `poly_half`
  - Even case circuit size bound proven
  - Even case evaluation equivalence: uses `liftCircuit_eval` and `verifier_iff`
  - Odd case circuit size bound proven (using `liftCircuitTo`)
  - Odd case evaluation equivalence: uses `liftCircuitTo_eval` and `verifier_iff`
  - Witness direction: uses `verifier_iff` directly
- **Remaining:**
  - Well-formedness for circuits from `inP` (2 sorries: one in even case, one in odd case)

---

## Blockers

1. **Well-formedness for circuits from inP:** Need to prove that circuits from `inP` (which correctly compute a language) must be well-formed.
   - **Analysis:** This may not be true for constant languages (e.g., `L n inp = false` for all `inp`), which can have circuits with `Var idx` nodes where `idx >= n`.
   - **Impact:** Without well-formedness, `liftCircuit_eval` and `liftCircuitTo_eval` are not true in general.
   - **Possible solutions:**
     - Prove that circuits from `inP` are well-formed (if possible)
     - Modify the circuit model to disallow `Var idx` nodes with `idx >= n`
     - Use a different circuit construction that doesn't require well-formedness
     - Accept well-formedness as an assumption and document the limitation

---

## Current Sorries

1. **Line 370:** Well-formedness for circuit `c` in even case of `p_subset_np`
2. **Line 430:** Well-formedness for circuit `c` in odd case of `p_subset_np`

Total: 2 sorries (both for well-formedness)

---

## Recommended Next Steps

1. **Prove well-formedness for circuits from inP:**
   - Analyze whether circuits from `inP` must be well-formed
   - If not, consider modifying the circuit model or using a different approach
   - If yes, prove it using the correctness condition `hc_correct`

2. **Alternative approach without well-formedness:**
   - Instead of using `liftCircuit` and `liftCircuitTo`, construct a new circuit that explicitly reads only from the first `m/2` inputs
   - This circuit would be well-formed by construction
   - This might be more complex but would avoid the well-formedness issue

---

## Files Modified

- `proofs/p_subset_np/circuit-lifting/Proof.lean`:
  - Added `IsWellFormed` predicate for circuits
  - Added `liftCircuitTo` and `liftCircuitTo_size` for general circuit lifting
  - Added `liftCircuitTo_eval` theorem (identical proof to `liftCircuit_eval`)
  - Moved `IsWellFormed` definition before `liftCircuitTo_eval` to avoid forward reference
  - Modified `liftCircuit_eval` to take well-formedness assumption
  - Proved `verifier_iff` using nested `Eq.rec` with dependent-type bookkeeping
  - Completed even and odd cases in `p_subset_np` (except for well-formedness)
- `proofs/p_subset_np/circuit-lifting/NOTES.md`: This file, updated to reflect current state

---

## Technical Context

- **Language definition:** `∀ (n : Nat), (Fin n → Bool) → Prop` uses dependent types
- **Circuit model:** `BoolCircuit n` with `Array CircuitNode` and evaluation via `Array.foldl`
- **Key insight:** `liftCircuit` preserves the gate array, so evaluation only depends on the first `n` inputs
- **Challenge:** Lean's dependent types make it hard to prove equivalences between `L m f` and `L n g` when `m = n` and `f` and `g` are related by `Fin.cast`
- **Solution for `verifier_iff`:** Used nested `Eq.rec` with carefully chosen motives to handle the dependent-type bookkeeping
