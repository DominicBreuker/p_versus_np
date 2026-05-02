# Progress Notes — P ⊆ NP

**Last Updated:** 2026-04-30 (Pass 2/2: Verification)

**Track role:** Supporting subproblem for the main P vs NP proof route.

**Status:** Complete — `Proof.lean` now proves `p_subset_np` with no `sorry`s.

---

## Current State

- `liftCircuit`, `liftCircuitTo`, their size lemmas, both lifting-evaluation lemmas, `poly_half`, `verifier_iff`, and `p_subset_np` are all proven.
- The lifting-evaluation lemmas still correctly require an `IsWellFormed` hypothesis.
- The main theorem now discharges that side condition by sanitizing the source circuit before lifting it.

### New proof step: circuit sanitization

- Added `sanitizeGate`, `sanitizeNode`, and `sanitizeCircuit`.
- Any out-of-bounds `Gate.Var idx` is rewritten to `Gate.Const false`.
- This preserves semantics for `BoolCircuit n` because `evalNode` already returns `false` when `idx ≥ n`.
- Proved:
  - `evalNode_sanitizeNode`
  - `sanitizeCircuit_size`
  - `sanitizeCircuit_wf`
  - `evalCircuit_sanitizeCircuit`

### Effect on `p_subset_np`

- In both the even and odd size branches, the proof now lifts `sanitizeCircuit c` instead of the raw circuit `c`.
- This gives the needed well-formedness hypothesis for `liftCircuit_eval` and `liftCircuitTo_eval`.
- Correctness is preserved by `evalCircuit_sanitizeCircuit`, so the original `hc_correct` witness still applies after rewriting.

---

## Blockers

- None in this target proof.

---

## Current Sorries

- None.

---

## Recommended Next Steps

1. Reuse this finished `p_subset_np` result from the main `p_versus_np/circuit_lower_bounds` track when verifier lifting is needed.
2. If the sanitization lemmas become shared infrastructure, move them into `lib/` in a separate cleanup task.

---

## Pass 2/2: Verification

**Date:** 2026-04-30

**Action:** Verified completion of pass 1/2 work and confirmed build success.

**Verification Results:**
- ✅ `lake build`: Build completed successfully (8350 jobs, no errors or warnings)
- ✅ `lean_diagnostic_messages`: No diagnostics for Proof.lean
- ✅ No `sorry` statements remain in Proof.lean
- ✅ All theorems compile without errors

**Findings:**
- The circuit_lifting proof is complete and correct
- `p_subset_np` theorem is fully proven with no placeholders
- All supporting lemmas (sanitization, lifting, polynomial bounds) are proven
- Build passes cleanly with no warnings

---

## Files Modified

- `proofs/p_subset_np/circuit_lifting/Proof.lean`
- `proofs/p_subset_np/circuit_lifting/NOTES.md`

---

## Technical Context

- A raw circuit for `BoolCircuit n` may contain `Gate.Var idx` with `idx ≥ n`; such gates evaluate to `false`.
- That means lifting the circuit is not evaluation-preserving unless the circuit is well-formed.
- Sanitization is the minimal repair: it preserves evaluation on size-`n` inputs and produces a well-formed circuit by construction.
