-- P vs NP via Circuit Complexity Lower Bounds
-- Idea: If NP-complete problems require superpolynomial circuits, then P ≠ NP.
-- Status: Fixed evalCircuit, added IsPolynomial, fixed inNP witness encoding.

-- Import shared library definitions
import PVsNp.Lib.Utils

open Fin
open PVsNpLib

namespace PVsNp.CircuitLowerBounds

/-- A simple gate type -/
inductive Gate where
  | And  : Gate
  | Or   : Gate
  | Not  : Gate
  | Var  : Nat → Gate   -- input variable index
  | Const : Bool → Gate
  deriving Repr, DecidableEq

/-- A circuit node: a gate applied to a list of children (by index into a node array) -/
structure CircuitNode where
  gate     : Gate
  children : List Nat   -- indices into the circuit's node list
  deriving Repr

/-- A Boolean circuit on n inputs: a list of nodes with a designated output node index -/
structure BoolCircuit (n : Nat) where
  nodes  : Array CircuitNode
  output : Nat   -- index of the output node
  deriving Repr

/-- The size of a circuit is the number of nodes -/
def circuitSize {n : Nat} (c : BoolCircuit n) : Nat := c.nodes.size

-- ---------------------------------------------------------------------------
-- Semantics (evaluation)
-- ---------------------------------------------------------------------------

/-- Evaluate a single node given an input assignment and previously computed values -/
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

/-- Evaluate a circuit on a given input by folding left over the node array.
    Nodes are assumed to be in topological order (children have smaller indices than parents).
    For each node, we compute its value based on the current accumulation of values. -/
def evalCircuit {n : Nat} (c : BoolCircuit n) (inp : Fin n → Bool) : Bool :=
  let vals := c.nodes.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
  vals.getD c.output false

-- ---------------------------------------------------------------------------
-- Sanity lemmas for evalCircuit
-- ---------------------------------------------------------------------------

/-- A circuit with a single Const true node evaluates to true. -/
lemma evalCircuit_const_true :
    let c : BoolCircuit 0 := {
      nodes := #[{ gate := Gate.Const true, children := [] }]
      output := 0
    }
    evalCircuit c (fun i => false) = true := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single Const false node evaluates to false. -/
lemma evalCircuit_const_false :
    let c : BoolCircuit 0 := {
      nodes := #[{ gate := Gate.Const false, children := [] }]
      output := 0
    }
    evalCircuit c (fun i => false) = false := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single Var node (input 0) evaluates to the input value.
    Requires n > 0. -/
lemma evalCircuit_var_zero {n : Nat} (hn : n > 0) (inp : Fin n → Bool) :
    let c : BoolCircuit n := {
      nodes := #[{ gate := Gate.Var 0, children := [] }]
      output := 0
    }
    evalCircuit c inp = inp ⟨0, hn⟩ := by
  simp [evalCircuit, evalNode, hn]

-- ---------------------------------------------------------------------------
-- Complexity classes (abstract stubs)
-- ---------------------------------------------------------------------------

/-- A language (decision problem) on bitstrings of length n -/
def Language := ∀ (n : Nat), (Fin n → Bool) → Prop

/-- L is in P if there is a polynomial p and a circuit family of size ≤ p(n) deciding L -/
def inP (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (_is_polynomial : IsPolynomial p),
  ∀ n, ∃ (c : BoolCircuit n), circuitSize c ≤ p n ∧
        ∀ inp, (evalCircuit c inp = true ↔ L n inp)

/-- L is in NP if witnesses are polynomial and verifiable in polynomial time -/
def inNP (L : Language) : Prop :=
  ∃ (V : Language), inP V ∧
  ∀ n inp, (L n inp ↔ ∃ w : Fin n → Bool,
    V (2 * n) (fun i =>
      if h : i.val < n then inp ⟨i.val, h⟩
      else w ⟨i.val - n, by omega⟩))

-- ---------------------------------------------------------------------------
-- Main conjecture
-- ---------------------------------------------------------------------------

/-- P ≠ NP: there exists a language in NP not in P -/
theorem p_neq_np : ∃ L : Language, inNP L ∧ ¬ inP L := by
  sorry

end PVsNp.CircuitLowerBounds

/-- A circuit with a single NOT gate evaluates to the negation of its child. -/
lemma evalCircuit_not {n : Nat} (c : Nat) (hc : c < n) (inp : Fin n → Bool) :
    let circuit : BoolCircuit n := {
      nodes := #[
        { gate := Gate.Var c, children := [] },
        { gate := Gate.Not, children := [0] }
      ]
      output := 1
    }
    evalCircuit circuit inp = !inp ⟨c, hc⟩ := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single AND gate with two constant true children evaluates to true. -/
lemma evalCircuit_and_true_true {n : Nat} :
    let circuit : BoolCircuit n := {
      nodes := #[
        { gate := Gate.Const true, children := [] },
        { gate := Gate.Const true, children := [] },
        { gate := Gate.And, children := [0, 1] }
      ]
      output := 2
    }
    evalCircuit circuit (fun i => false) = true := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single AND gate with one true and one false child evaluates to false. -/
lemma evalCircuit_and_true_false {n : Nat} :
    let circuit : BoolCircuit n := {
      nodes := #[
        { gate := Gate.Const true, children := [] },
        { gate := Gate.Const false, children := [] },
        { gate := Gate.And, children := [0, 1] }
      ]
      output := 2
    }
    evalCircuit circuit (fun i => false) = false := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single OR gate with two constant false children evaluates to false. -/
lemma evalCircuit_or_false_false {n : Nat} :
    let circuit : BoolCircuit n := {
      nodes := #[
        { gate := Gate.Const false, children := [] },
        { gate := Gate.Const false, children := [] },
        { gate := Gate.Or, children := [0, 1] }
      ]
      output := 2
    }
    evalCircuit circuit (fun i => false) = false := by
  simp [evalCircuit, evalNode]
  rfl

/-- A circuit with a single OR gate with one true and one false child evaluates to true. -/
lemma evalCircuit_or_true_false {n : Nat} :
    let circuit : BoolCircuit n := {
      nodes := #[
        { gate := Gate.Const true, children := [] },
        { gate := Gate.Const false, children := [] },
        { gate := Gate.Or, children := [0, 1] }
      ]
      output := 2
    }
    evalCircuit circuit (fun i => false) = true := by
  simp [evalCircuit, evalNode]
  rfl

-- ---------------------------------------------------------------------------
-- Cook–Levin Theorem (axiomatized)
-- ---------------------------------------------------------------------------

/-- The Cook–Levin theorem states that SAT is NP-complete.
    We axiomatize this as it requires substantial formalization work. -/
axiom sat_is_np_complete :
    ∃ (sat : Language), inNP sat ∧ 
    ∀ (L : Language), inNP L → ∃ (f : Nat → Nat) (_hf : IsPolynomial f),
      ∀ n inp, L n inp ↔ sat (f n) (fun i => 
        if h : i.val < n then inp ⟨i.val, h⟩
        else false)

-- ---------------------------------------------------------------------------
-- Connection between circuit lower bounds and P ≠ NP
-- ---------------------------------------------------------------------------

/-- If SAT requires superpolynomial circuit size, then P ≠ NP.
    This is the key connection between circuit complexity and the P vs NP problem. -/
lemma sat_superpolynomial_implies_p_neq_np
    (sat : Language) 
    (h_sat_np : inNP sat)
    (h_superpoly : ∃ (c : ℕ), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n) :
    ∃ L : Language, inNP L ∧ ¬ inP L := by
  -- Use SAT as our witness language
  use sat
  constructor
  -- SAT is in NP (given)
  exact h_sat_np
  -- SAT is not in P (by contradiction)
  intro h_sat_in_p
  -- Extract the polynomial bound from h_sat_in_p
  obtain ⟨p, hp_poly, h_dec⟩ := h_sat_in_p
  -- Get the superpolynomial witness
  obtain ⟨c, hc⟩ := h_superpoly
  -- For sufficiently large n, any circuit deciding SAT has size > p n
  -- But h_dec says there exists a circuit of size ≤ p n
  -- This is a contradiction
  sorry
