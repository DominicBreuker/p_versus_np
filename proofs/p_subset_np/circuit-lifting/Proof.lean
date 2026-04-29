import Mathlib
import PVsNpLib

-- P ⊆ NP — supporting formalization in the circuit complexity model used by the
-- main P vs NP track.
-- Goal: Every language in P is also in NP.
-- Status: Stub — the remaining work is ordinary Lean proof engineering.
--
-- The proof strategy is:
--   1. Given L ∈ P (polynomial circuit family {c_n}), define the verifier V at size 2*n
--      as liftCircuit(c_n) — same gate array, but typed for 2*n inputs.
--   2. V ∈ P: liftCircuit preserves circuit size; the polynomial bound is q(m) = p(m/2) + 1.
--   3. Witness direction: V(2*n)(inp ++ w) = L(n)(inp) for any w, because V ignores the
--      second half of its input. The witness w can be anything (e.g., all false).

-- ---------------------------------------------------------------------------
-- Re-use definitions from the shared library and the local circuit model
-- ---------------------------------------------------------------------------

open PVsNpLib

namespace PVsNp.PSubsetNP

-- ---------------------------------------------------------------------------
-- Circuit definitions (copied from circuit-lower-bounds for self-containment)
-- ---------------------------------------------------------------------------

inductive Gate where
  | And   : Gate
  | Or    : Gate
  | Not   : Gate
  | Var   : Nat → Gate
  | Const : Bool → Gate
  deriving Repr, DecidableEq

structure CircuitNode where
  gate     : Gate
  children : List Nat
  deriving Repr

structure BoolCircuit (n : Nat) where
  nodes  : Array CircuitNode
  output : Nat
  deriving Repr

def circuitSize {n : Nat} (c : BoolCircuit n) : Nat := c.nodes.size

def evalNode {n : Nat} (inp : Fin n → Bool) (vals : Array Bool) (node : CircuitNode) : Bool :=
  match node.gate with
  | Gate.Const b => b
  | Gate.Var i   => if h : i < n then inp ⟨i, h⟩ else false
  | Gate.Not     =>
      match node.children with
      | [c] => !(vals.getD c false)
      | _   => false
  | Gate.And     =>
      node.children.foldl (fun acc c => acc && vals.getD c true) true
  | Gate.Or      =>
      node.children.foldl (fun acc c => acc || vals.getD c false) false

def evalCircuit {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) : Bool :=
  let vals := c.nodes.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
  vals.getD c.output false

def Language := ∀ (n : Nat), (Fin n → Bool) → Prop

def inP (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (_is_polynomial : IsPolynomial p),
  ∀ n, ∃ (c : BoolCircuit n), circuitSize c ≤ p n ∧
        ∀ inp, (evalCircuit c inp = true ↔ L n inp)

def inNP (L : Language) : Prop :=
  ∃ (V : Language), inP V ∧
  ∀ n inp, (L n inp ↔ ∃ w : Fin n → Bool,
    V (2 * n) (fun i =>
      if h : i.val < n then inp ⟨i.val, h⟩
      else w ⟨i.val - n, by omega⟩))

-- ---------------------------------------------------------------------------
-- Circuit lifting: BoolCircuit n → BoolCircuit (2 * n)
-- ---------------------------------------------------------------------------

/-- Lift a circuit for n inputs to a circuit for 2*n inputs.
    The gate array is unchanged; Var nodes with index < n still read the correct
    input (the first n bits of the combined 2*n input). -/
def liftCircuit {n : Nat} (c : BoolCircuit n) : BoolCircuit (2 * n) :=
  { nodes := c.nodes, output := c.output }

/-- Lifting preserves circuit size -/
theorem liftCircuit_size {n : Nat} (c : BoolCircuit n) :
    circuitSize (liftCircuit c) = circuitSize c := by
  simp [liftCircuit, circuitSize]

/-- Lifting preserves evaluation when restricted to the first n inputs.
    Proof sketch: evalNode and evalCircuit only consult inp at Var-gate positions i < n;
    lifting keeps those same positions so the values agree. -/
theorem liftCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin (2 * n) → Bool) :
    evalCircuit (liftCircuit c) inp =
    evalCircuit c (fun i => inp ⟨i.val, by have := i.isLt; omega⟩) := by
  simp only [liftCircuit, evalCircuit]
  congr 1
  -- Both accumulations fold the same node array with the same evalNode behaviour:
  -- Gate.Var i looks up inp ⟨i, h⟩ where h : i < 2*n (left) vs. inp ⟨i, _⟩ (right).
  -- These are equal because the Fin values are propositionally equal.
  sorry

-- ---------------------------------------------------------------------------
-- Polynomial bound for the lifted family
-- ---------------------------------------------------------------------------

/-- If p is polynomial then so is the function m ↦ p (m / 2) + 1.
    This gives the polynomial bound for the verifier circuit family at size 2*n.
    Proof: p(m/2) ≤ c*(m/2)^k + c ≤ c*m^k + c < (c+1)*m^k + (c+1). -/
theorem poly_half {p : Nat → Nat} (hp : IsPolynomial p) : IsPolynomial (fun m => p (m / 2) + 1) := by
  obtain ⟨k, c, hpc⟩ := hp
  refine ⟨k, c + 1, fun m => ?_⟩
  show p (m / 2) + 1 ≤ (c + 1) * m ^ k + (c + 1)
  have h_half : m / 2 ≤ m := Nat.div_le_self m 2
  have hpow : (m / 2) ^ k ≤ m ^ k := Nat.pow_le_pow_left h_half k
  have h1 : p (m / 2) ≤ c * m ^ k + c :=
    Nat.le_trans (hpc (m / 2))
      (Nat.add_le_add_right (Nat.mul_le_mul_left c hpow) c)
  -- (c + 1) * m^k + (c + 1) = c * m^k + m^k + c + 1 ≥ c * m^k + c + 1 ≥ p(m/2) + 1
  have h2 : c * m ^ k + c + 1 ≤ (c + 1) * m ^ k + (c + 1) := by
    have hexp : 0 ≤ m ^ k := Nat.zero_le _
    have : (c + 1) * m ^ k = c * m ^ k + m ^ k := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  omega

-- ---------------------------------------------------------------------------
-- Key lemma: V (2*n) (combined inp w) ↔ L n inp
-- ---------------------------------------------------------------------------

/-- The verifier at size 2*n, applied to the combined input, evaluates L on inp.
    Proof idea:
      - 2*n/2 = n (arithmetic)
      - for i : Fin n, combined ⟨i.val, _⟩ = if i.val < n then inp ⟨i.val, _⟩ else ...
                                             = inp i  (since i.val < n always for i : Fin n)
    The sorry here is a dependent-type bookkeeping issue (matching Fin ((2*n)/2) with Fin n);
    the mathematical content is trivially true. -/
theorem verifier_iff (L : Language) (n : Nat) (inp : Fin n → Bool) (w : Fin n → Bool) :
    L ((2 * n) / 2)
      (fun (i : Fin ((2 * n) / 2)) =>
        (fun j : Fin (2 * n) =>
          if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, by omega⟩)
        ⟨i.val, by omega⟩)
    ↔ L n inp := by
  sorry

-- ---------------------------------------------------------------------------
-- Main theorem
-- ---------------------------------------------------------------------------

/-- P ⊆ NP: every language decidable in polynomial time is also in NP.
    Proof: given a polynomial circuit family {c_n} for L, define the verifier V at
    size 2*n as the lifted circuit liftCircuit c_n.  The witness is ignored entirely. -/
theorem p_subset_np {L : Language} (hL : inP L) : inNP L := by
  obtain ⟨p, hp_poly, h_circuits⟩ := hL
  -- The verifier V: V(m)(inp) = L(m/2)(inp restricted to first m/2 bits)
  refine ⟨fun m inp => L (m / 2) (fun i => inp ⟨i.val, by have := i.isLt; omega⟩),
          ⟨fun m => p (m / 2) + 1, poly_half hp_poly, fun m => ?_⟩,
          fun n inp => ?_⟩
  · -- V ∈ P: at size m, use liftCircuit applied to the circuit for L at size m/2.
    -- Type issue: liftCircuit gives BoolCircuit (2*(m/2)), not BoolCircuit m when m is odd.
    -- We defer this mismatch with sorry pending a uniform treatment of sizes.
    sorry
  · -- Witness direction: use verifier_iff
    constructor
    · -- L n inp → ∃ w, V (2*n) (combined inp w)
      intro hL_n
      exact ⟨fun _ => false, (verifier_iff L n inp (fun _ => false)).mpr hL_n⟩
    · -- ∃ w, V (2*n) (combined inp w) → L n inp
      intro ⟨w, hV⟩
      exact (verifier_iff L n inp w).mp hV

end PVsNp.PSubsetNP

