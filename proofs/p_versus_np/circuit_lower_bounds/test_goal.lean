import Mathlib
import PVsNpLib

open Fin
open PVsNpLib

namespace PVsNp.CircuitLowerBounds

inductive Gate where
  | And  : Gate
  | Or   : Gate
  | Not  : Gate
  | Var  : Nat → Gate
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

inductive NodeCode (n s : Nat) where
  | const : Bool → NodeCode n s
  | var : Fin n → NodeCode n s
  | not : Fin s → NodeCode n s
  | and : Finset (Fin s) → NodeCode n s
  | or : Finset (Fin s) → NodeCode n s
deriving DecidableEq, Fintype

abbrev NormalizedCircuit (n s : Nat) := Option (Fin s) × (Fin s → NodeCode n s)

private def falseNode : CircuitNode := ⟨Gate.Const false, []⟩

private noncomputable def nodeCodeToRaw {n s : Nat} : NodeCode n s → CircuitNode
  | .const b => ⟨Gate.Const b, []⟩
  | .var v => ⟨Gate.Var v.val, []⟩
  | .not child => ⟨Gate.Not, [child.val]⟩
  | .and children => ⟨Gate.And, children.toList.map Fin.val⟩
  | .or children => ⟨Gate.Or, children.toList.map Fin.val⟩

private noncomputable def normalizedToRaw {n s : Nat} (c : NormalizedCircuit n s) : BoolCircuit n :=
  { nodes := Array.ofFn (fun i => nodeCodeToRaw (c.2 i))
    output := match c.1 with
      | some out => out.val
      | none => s }

private def normalizeCircuit {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s) :
    NormalizedCircuit n s :=
  let pre : Fin c.nodes.size → NodeCode n s := fun i => 
    match c.nodes[i] with
    | ⟨Gate.Const b, []⟩ => .const b
    | ⟨Gate.Var i, []⟩ => if h : i < n then .var ⟨i, h⟩ else .const false
    | ⟨Gate.Not, [child]⟩ => if h : child < s then .not ⟨child, h⟩ else .const true
    | ⟨Gate.Not, _⟩ => .const false
    | ⟨Gate.And, children⟩ => .and (c.nodes[i].children.filterMap (fun child => if h : child < s then some ⟨child, h⟩ else none)).toFinset
    | ⟨Gate.Or, children⟩ => .or (c.nodes[i].children.filterMap (fun child => if h : child < s then some ⟨child, h⟩ else none)).toFinset
  let suf : Fin (s - c.nodes.size) → NodeCode n s := fun _ => .const false;
  let hsplit : c.nodes.size + (s - c.nodes.size) = s := Nat.add_sub_of_le hsize;
  let nodes : Fin s → NodeCode n s := fun i => Fin.append pre suf (Fin.cast hsplit.symm i);
  let output : Option (Fin s) :=
    if h : c.output < c.nodes.size then some ⟨c.output, lt_of_lt_of_le h hsize⟩ else none;
  (output, nodes)

example {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s) :
    (normalizedToRaw (normalizeCircuit c hsize)).nodes = 
    List.ofFn (fun i : Fin c.nodes.size => 
      match c.nodes[i] with
      | ⟨Gate.Const b, []⟩ => .const b
      | ⟨Gate.Var i, []⟩ => if h : i < n then .var ⟨i, h⟩ else .const false
      | ⟨Gate.Not, [child]⟩ => if h : child < s then .not ⟨child, h⟩ else .const true
      | ⟨Gate.Not, _⟩ => .const false
      | ⟨Gate.And, children⟩ => .and (c.nodes[i].children.filterMap (fun child => if h : child < s then some ⟨child, h⟩ else none)).toFinset
      | ⟨Gate.Or, children⟩ => .or (c.nodes[i].children.filterMap (fun child => if h : child < s then some ⟨child, h⟩ else none)).toFinset) ++ 
    List.replicate (s - c.nodes.size) (.const false) := by
  unfold normalizedToRaw normalizeCircuit
  sorry

end PVsNp.CircuitLowerBounds
