# Progress Notes — P ⊆ NP

**Last Updated:** 2025-01-15

**Track role:** Supporting subproblem for the main P vs NP proof route.

**Status:** Active — file compiles with 3 sorries, well-formedness predicate added, `liftCircuitTo` added

---

## Current State

- `liftCircuit`, `liftCircuit_size`, `liftCircuitTo`, `liftCircuitTo_size`, and `poly_half` are fully proven.
- The proof file imports both `Mathlib` and `PVsNpLib`, maintaining clean shared imports.
- `IsWellFormed` predicate added to ensure circuits have valid Var node indices.
- `liftCircuit_eval` signature updated to take well-formedness assumption, `h_nodes` lemma proven.
- `liftCircuitTo` added to support lifting circuits to arbitrary larger sizes (needed for odd case in `p_subset_np`).
- File compiles successfully with only 3 sorries (no errors).

### `liftCircuit_eval` (line 103)
- **Status:** Partially proven - well-formedness predicate added and `h_nodes` lemma proven
- **Completed:**
  - Added `IsWellFormed` predicate: `∀ i < c.nodes.size, ∀ j, c.nodes[i]!.gate = Gate.Var j → j < n`
  - Modified theorem signature to take `h_wf : IsWellFormed c` as an argument
  - Proved helper lemma `h_nodes`: for all `i < c.nodes.size` and all `acc`, `evalNode inp acc c.nodes[i]! = evalNode (fun i => inp ⟨i.val, _⟩) acc c.nodes[i]!`
- **Remaining:**
  - Prove the foldl equality: the two foldl computations produce the same array
  - **Blocker:** Need a lemma about `Array.foldl` congruence for functions that agree on all elements of the array
  - **Approach:** The key lemma needed is: if `∀ x ∈ arr, f acc x = g acc x`, then `arr.foldl (fun acc x => acc.push (f acc x)) #[] = arr.foldl (fun acc x => acc.push (g acc x)) #[]`
  - **Note:** `Array.foldl_congr` exists in Mathlib but requires `f = g` as functions, not just agreement on array elements

### `verifier_iff` (line 188)
- **Status:** Not started - has sorry
- **Mathematical content:** Trivial - `(2*n)/2 = n` and the functions are pointwise equal
- **Challenge:** Dependent-type bookkeeping in Lean
- **Key insight:** For `i : Fin ((2*n)/2)`, we have `i.val < n`, so:
  - Combined function at `i`: `(fun j => if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, _⟩) ⟨i.val, _⟩ = inp ⟨i.val, _⟩`
  - This equals `inp (Fin.cast h_div i)` where `h_div : (2*n)/2 = n`
  - So combined function = `inp ∘ Fin.cast h_div`
- **Goal:** Prove `L ((2*n)/2) (inp ∘ Fin.cast h_div) ↔ L n inp`
- **Solution:** Use `Eq.rec` to transport `L` along `h_div` with a motive that handles the function transport:
  ```lean
  have h_func_transport : Eq.rec (motive := fun k _ => Fin k → Bool) (inp ∘ Fin.cast h_div) h_div = inp := ...
  have h_L_transport : L ((2*n)/2) (inp ∘ Fin.cast h_div) = L n (Eq.rec ... h_div) := Eq.rec ...
  rw [h_L_transport, h_func_transport]
  ```

### `p_subset_np` (line 212)
- **Status:** Partially proven - structure in place, uses well-formedness and `liftCircuitTo`
- **Completed:**
  - Verifier definition: `V(m)(inp) = L(m/2)(inp restricted to first m/2 bits)`
  - Polynomial bound: `p(m/2) + 1` with proof `poly_half`
  - Even case circuit size bound proven
  - Odd case circuit size bound proven (using `liftCircuitTo`)
  - Witness direction structure in place (uses `verifier_iff`)
- **Remaining:**
  - Even case evaluation equivalence: blocked by `liftCircuit_eval` and `verifier_iff`
  - Odd case evaluation equivalence: need a version of `liftCircuit_eval` for `liftCircuitTo`
  - Well-formedness for circuits from `inP`: need to prove that circuits from `inP` are well-formed

---

## Blockers

1. **Array.foldl congruence:** `liftCircuit_eval` needs a lemma that if two functions agree on all elements of an array, then `foldl` with those functions produces equal results. `Array.foldl_congr` requires function equality, not just pointwise agreement on the array.

2. **Dependent-type bookkeeping:** `verifier_iff` requires transporting a proposition `L m f` along an equality `m = n` while also transporting the function `f : Fin m → Bool` to `Fin n → Bool`. This is non-trivial in Lean's dependent type system.

3. **Well-formedness for circuits from inP:** Need to prove that circuits from `inP` (which correctly compute a language) must be well-formed. This is reasonable because Var nodes with `idx >= n` always return `false` and cannot contribute to computing any non-trivial language.

---

## Recommended Next Steps

1. **Complete `verifier_iff`:** This is the most fundamental blocker. The proof requires:
   - Showing that the combined function equals `inp ∘ Fin.cast h_div`
   - Using `Eq.rec` to transport `L` along `h_div`
   - Proving that the transported function equals `inp`

2. **Complete `liftCircuit_eval`:** Once `verifier_iff` is done, this can be completed by:
   - Proving a general lemma about `Array.foldl` congruence for functions that agree on array elements
   - Or using induction on the array with `h_nodes`

3. **Prove well-formedness for circuits from inP:** Add an assumption or prove that circuits from `inP` are well-formed.

4. **Complete `p_subset_np`:** Once the above are done:
   - Even case: Use `liftCircuit_eval` and `verifier_iff`
   - Odd case: Prove a version of `liftCircuit_eval` for `liftCircuitTo`

---

## Files Modified

- `proofs/p_subset_np/circuit-lifting/Proof.lean`:
  - Added `IsWellFormed` predicate for circuits
  - Added `liftCircuitTo` and `liftCircuitTo_size` for general circuit lifting
  - Modified `liftCircuit_eval` to take well-formedness assumption
  - Proved helper lemma `h_nodes` for `liftCircuit_eval`
  - Updated `p_subset_np` to use `liftCircuitTo` for odd case
  - Added clear TODOs for remaining work
- `proofs/p_subset_np/circuit-lifting/NOTES.md`: This file, updated to reflect current state

---

## Current Sorries

1. **Line 119:** `liftCircuit_eval` - Array.foldl congruence proof
2. **Line 191:** `verifier_iff` - Dependent-type bookkeeping
3. **Line 212:** `p_subset_np` - Main theorem (blocked by 1 and 2)

---

## Technical Context

- **Language definition:** `∀ (n : Nat), (Fin n → Bool) → Prop` uses dependent types
- **Circuit model:** `BoolCircuit n` with `Array CircuitNode` and evaluation via `Array.foldl`
- **Key insight:** `liftCircuit` preserves the gate array, so evaluation only depends on the first `n` inputs
- **Challenge:** Lean's dependent types make it hard to prove equivalences between `L m f` and `L n g` when `m = n` and `f` and `g` are related by `Fin.cast`

## Technical Interruptions

- 2026-04-30 02:20 UTC — Researcher workflow hit a technical interruption: Mistral Vibe timed out during pass 2/2 after 1800 seconds.. Partial work from this run was preserved; review the current proof state before continuing.
- 2026-04-30 07:55 UTC — Researcher workflow hit a technical interruption: Mistral Vibe timed out during pass 1/2 after 1800 seconds.. Partial work from this run was preserved; review the current proof state before continuing.
