-- Utility lemmas and shared definitions for P vs NP research
-- Extend this file with reusable code that multiple ideas share.

namespace PVsNpLib

-- ---------------------------------------------------------------------------
-- Common type aliases
-- ---------------------------------------------------------------------------

/-- A Boolean function on n inputs -/
abbrev BoolFn (n : Nat) := (Fin n → Bool) → Bool

-- ---------------------------------------------------------------------------
-- Polynomial predicate
-- ---------------------------------------------------------------------------

/-- A function is polynomial if it is bounded by c * n^k + c for some constants -/
def IsPolynomial (p : Nat → Nat) : Prop :=
  ∃ k c : Nat, ∀ n, p n ≤ c * n ^ k + c

-- ---------------------------------------------------------------------------
-- Combinatorics stubs (to be developed by researchers)
-- ---------------------------------------------------------------------------

/-- Placeholder: Shannon counting argument — most Boolean functions need large circuits. -/
theorem shannon_counting_argument_placeholder : True := trivial

end PVsNpLib
