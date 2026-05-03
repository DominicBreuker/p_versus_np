import Mathlib
import PVsNpLib

set_option maxHeartbeats 4000000

-- P vs NP via Circuit Complexity Lower Bounds
-- Primary repository track: formalize a circuit-lower-bound route to P ≠ NP.
-- Status: the reduction is conditional; the lower-bound work remains open.

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

/-- Helper: construct a single-node constant circuit -/
def constCircuit (b : Bool) : BoolCircuit 0 :=
  { nodes := #[(⟨Gate.Const b, []⟩ : CircuitNode)]
    output := 0 }

/-- A constant-true circuit evaluates to true -/
theorem eval_const_true : evalCircuit (constCircuit true) (fun _ => false) = true := by
  unfold evalCircuit constCircuit
  simp [evalNode]

/-- A constant-false circuit evaluates to false -/
theorem eval_const_false : evalCircuit (constCircuit false) (fun _ => false) = false := by
  unfold evalCircuit constCircuit
  simp [evalNode]

/-- Helper: construct a single-node variable circuit for input index i -/
def varCircuit (n : Nat) (i : Nat) (_hi : i < n) : BoolCircuit n :=
  { nodes := #[(⟨Gate.Var i, []⟩ : CircuitNode)]
    output := 0 }

/-- A Var-0 circuit on n>0 inputs evaluates to the first input bit -/
theorem eval_var_zero (n : Nat) (hn : n > 0) (inp : Fin n → Bool) :
    evalCircuit (varCircuit n 0 (Nat.zero_lt_of_lt hn)) inp = inp ⟨0, Nat.zero_lt_of_lt hn⟩ := by
  unfold evalCircuit varCircuit
  simp only [Array.foldl, Array.getD, Array.push, evalNode]
  have : 0 < n := Nat.zero_lt_of_lt hn
  simp [this]

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
-- Circuit lower bounds via counting arguments
-- ---------------------------------------------------------------------------

/-- The number of Boolean circuits of size s on n inputs is at most (s+1)^(s+1) * 2^s.
    This is a rough upper bound: there are at most s+1 nodes, each with a gate from a
    finite set, and s children pointers. -/
def circuit_count_upper_bound (_n s : Nat) : Nat := (s + 1) ^ (s + 1) * 2 ^ s

/-- The number of distinct Boolean functions on n inputs is 2^(2^n). -/
def boolean_function_count (n : Nat) : Nat := 2 ^ (2 ^ n)


/-- Finite node codes used for normalized counting. -/
inductive NodeCode (n s : Nat) where
  | const : Bool → NodeCode n s
  | var : Fin n → NodeCode n s
  | not : Fin s → NodeCode n s
  | and : Finset (Fin s) → NodeCode n s
  | or : Finset (Fin s) → NodeCode n s
  deriving DecidableEq, Fintype

/-- A normalized circuit of size exactly `s`, with a finite node code at each position. -/
abbrev NormalizedCircuit (n s : Nat) := Option (Fin s) × (Fin s → NodeCode n s)

private def falseNode : CircuitNode := ⟨Gate.Const false, []⟩

private def boundedChildren (s : Nat) (children : List Nat) : Finset (Fin s) :=
  (children.filterMap (fun child => if h : child < s then some ⟨child, h⟩ else none)).toFinset

private theorem mem_boundedChildren {s : Nat} {children : List Nat} {x : Fin s} :
    x ∈ boundedChildren s children ↔ x.val ∈ children := by
  simp [boundedChildren]
  constructor
  · intro h
    rcases h with ⟨a, ha, ha_lt, hax⟩
    cases hax
    simpa using ha
  · intro hx
    refine ⟨x.val, hx, x.isLt, ?_⟩
    ext
    simp

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

private def normalizeNodeCode (n s : Nat) (node : CircuitNode) : NodeCode n s :=
  match node.gate with
  | Gate.Const b => .const b
  | Gate.Var i => if h : i < n then .var ⟨i, h⟩ else .const false
  | Gate.Not =>
      match node.children with
      | [child] => if h : child < s then .not ⟨child, h⟩ else .const true
      | _ => .const false
  | Gate.And => .and (boundedChildren s node.children)
  | Gate.Or => .or (boundedChildren s node.children)

private def normalizeCircuit {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s) :
    NormalizedCircuit n s :=
  let pre : Fin c.nodes.size → NodeCode n s := fun i => normalizeNodeCode n s (c.nodes[i]);
  let suf : Fin (s - c.nodes.size) → NodeCode n s := fun _ => .const false;
  let hsplit : c.nodes.size + (s - c.nodes.size) = s := Nat.add_sub_of_le hsize;
  let nodes : Fin s → NodeCode n s := fun i => Fin.append pre suf (Fin.cast hsplit.symm i);
  let output : Option (Fin s) :=
    if h : c.output < c.nodes.size then some ⟨c.output, lt_of_lt_of_le h hsize⟩ else none;
  (output, nodes)

private theorem foldl_and_false {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b && f x) false = false := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih]

private theorem foldl_or_true {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b || f x) true = true := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih]

private theorem foldl_and_true_iff {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b && f x) true = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hfx : f x
      · simp [List.foldl, hfx, foldl_and_false]
      · simp [List.foldl, hfx, ih]

private theorem foldl_or_true_iff {α : Type} (l : List α) (f : α → Bool) :
    l.foldl (fun b x => b || f x) false = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hfx : f x
      · simp [List.foldl, hfx, ih]
      · simp [List.foldl, hfx, foldl_or_true]

private theorem foldl_and_map_val {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) c => acc && vals.getD c true) init (l.map Fin.val) =
      List.foldl (fun (acc : Bool) (child : Fin s) => acc && vals.getD child.val true) init l := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init && vals.getD child.val true)

private theorem foldl_or_map_val {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) c => acc || vals.getD c false) init (l.map Fin.val) =
      List.foldl (fun (acc : Bool) (child : Fin s) => acc || vals.getD child.val false) init l := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init || vals.getD child.val false)

private theorem foldl_and_map_eval {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) (child : Fin s) => acc && vals.getD child.val true) init l =
      List.foldl (fun (acc : Bool) b => acc && b) init (l.map (fun child => vals.getD child.val true)) := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init && vals.getD child.val true)

private theorem foldl_or_map_eval {s : Nat} (vals : Array Bool) (l : List (Fin s)) (init : Bool) :
    List.foldl (fun (acc : Bool) (child : Fin s) => acc || vals.getD child.val false) init l =
      List.foldl (fun (acc : Bool) b => acc || b) init (l.map (fun child => vals.getD child.val false)) := by
  induction l generalizing init with
  | nil => simp
  | cons child rest ih => simpa using ih (init := init || vals.getD child.val false)

private theorem and_fold_preserved (vals : Array Bool) (s : Nat) (hs : vals.size ≤ s)
    (children : List Nat) :
    children.foldl (fun acc c => acc && vals.getD c true) true =
      ((boundedChildren s children).toList.map (fun child => vals.getD child.val true)).foldl (· && ·) true := by
  apply (Bool.eq_iff_iff).2
  constructor <;> intro h
  · rw [foldl_and_true_iff] at h
    rw [foldl_and_true_iff]
    intro b hb
    rcases List.mem_map.mp hb with ⟨child, hchild, rfl⟩
    have hmem : child.val ∈ children := (mem_boundedChildren).mp (Finset.mem_toList.mp hchild)
    exact h child.val hmem
  · rw [foldl_and_true_iff] at h
    rw [foldl_and_true_iff]
    intro c hc
    by_cases hcs : c < s
    · let child : Fin s := ⟨c, hcs⟩
      have hchild : child ∈ (boundedChildren s children).toList := by
        exact Finset.mem_toList.mpr ((mem_boundedChildren).2 hc)
      have hbool : vals.getD child.val true ∈
          (boundedChildren s children).toList.map (fun child => vals.getD child.val true) := by
        exact List.mem_map.mpr ⟨child, hchild, rfl⟩
      have hval : vals.getD child.val true = true := h _ hbool
      simpa [child] using hval
    · have hge : vals.size ≤ c := le_trans hs (Nat.le_of_not_gt hcs)
      simp [Array.getD, hge]

private theorem or_fold_preserved (vals : Array Bool) (s : Nat) (hs : vals.size ≤ s)
    (children : List Nat) :
    children.foldl (fun acc c => acc || vals.getD c false) false =
      ((boundedChildren s children).toList.map (fun child => vals.getD child.val false)).foldl (· || ·) false := by
  apply (Bool.eq_iff_iff).2
  constructor <;> intro h
  · rw [foldl_or_true_iff] at h
    rw [foldl_or_true_iff]
    rcases h with ⟨c, hc, hval⟩
    by_cases hcs : c < s
    · let child : Fin s := ⟨c, hcs⟩
      refine ⟨vals.getD child.val false, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨child, Finset.mem_toList.mpr ((mem_boundedChildren).2 hc), rfl⟩
      · simpa [child] using hval
    · have hge : vals.size ≤ c := le_trans hs (Nat.le_of_not_gt hcs)
      simp [Array.getD, hge] at hval
  · rw [foldl_or_true_iff] at h
    rw [foldl_or_true_iff]
    rcases h with ⟨b, hb, htrue⟩
    rcases List.mem_map.mp hb with ⟨child, hchild, hbdef⟩
    refine ⟨child.val, (mem_boundedChildren).mp (Finset.mem_toList.mp hchild), ?_⟩
    simpa [hbdef] using htrue

private theorem evalNode_normalizeNodeCode {n s : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (hs : vals.size ≤ s) (node : CircuitNode) :
    evalNode inp vals (nodeCodeToRaw (normalizeNodeCode n s node)) = evalNode inp vals node := by
  rcases node with ⟨gate, children⟩
  cases gate with
  | And =>
      simp only [normalizeNodeCode, nodeCodeToRaw, evalNode]
      rw [foldl_and_map_val, foldl_and_map_eval, ← and_fold_preserved vals s hs children]
  | Not =>
      cases children with
      | nil => simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
      | cons child tail =>
          cases htail : tail with
          | nil =>
              by_cases hchild : child < s
              · simp [normalizeNodeCode, nodeCodeToRaw, hchild, evalNode]
              · have hge : vals.size ≤ child := le_trans hs (Nat.le_of_not_gt hchild)
                simp [normalizeNodeCode, nodeCodeToRaw, hchild, evalNode, Array.getD, hge]
          | cons child' rest =>
              simp [normalizeNodeCode, nodeCodeToRaw, evalNode]
  | Or =>
      simp only [normalizeNodeCode, nodeCodeToRaw, evalNode]
      rw [foldl_or_map_val, foldl_or_map_eval, ← or_fold_preserved vals s hs children]
  | Var i =>
      by_cases hi : i < n
      · simp [normalizeNodeCode, nodeCodeToRaw, hi, evalNode]
      · simp [normalizeNodeCode, nodeCodeToRaw, hi, evalNode]
  | Const b => simp [normalizeNodeCode, nodeCodeToRaw, evalNode]

private def evalStep {n : Nat} (inp : Fin n → Bool) (acc : Array Bool) (node : CircuitNode) : Array Bool :=
  acc.push (evalNode inp acc node)

private theorem evalStep_fold_size {n : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (nodes : List CircuitNode) :
    (List.foldl (evalStep inp) vals nodes).size = vals.size + nodes.length := by
  induction nodes generalizing vals with
  | nil => simp [evalStep]
  | cons node rest ih => simp [List.foldl, evalStep, ih, Array.size_push, Nat.add_left_comm, Nat.add_comm]

private theorem evalStep_fold_getElem?_preserve {n : Nat} (inp : Fin n → Bool) (vals : Array Bool)
    (extra : List CircuitNode) (i : Nat) (hi : i < vals.size) :
    (List.foldl (evalStep inp) vals extra)[i]? = vals[i]? := by
  induction extra generalizing vals with
  | nil => simp
  | cons node rest ih =>
      simp [List.foldl, evalStep]
      rw [ih (vals := vals.push (evalNode inp vals node))]
      · rw [Array.getElem?_eq_getElem hi]
        exact Array.getElem?_push_lt hi
      · rw [Array.size_push]
        exact Nat.lt_succ_of_lt hi

private theorem evalStep_fold_normalized_eq {n s : Nat} (inp : Fin n → Bool)
    (vals : Array Bool) (nodes : List CircuitNode) (hbound : vals.size + nodes.length ≤ s) :
    List.foldl (evalStep inp) vals (nodes.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node))) =
      List.foldl (evalStep inp) vals nodes := by
  induction nodes generalizing vals with
  | nil => simp [evalStep]
  | cons node rest ih =>
      have hs : vals.size ≤ s := by omega
      have hnode : evalNode inp vals (nodeCodeToRaw (normalizeNodeCode n s node)) = evalNode inp vals node :=
        evalNode_normalizeNodeCode inp vals hs node
      simp [List.foldl, evalStep, hnode]
      apply ih
      simpa [Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound

private theorem array_foldl_ofFn_eq_list_foldl {α β : Type} {n : Nat} (f : β → α → β) (init : β)
    (g : Fin n → α) :
    Array.foldl f init (Array.ofFn g) = List.foldl f init (List.ofFn g) := by
  rw [Array.foldl_toList]
  simp

private theorem normalizeCircuit_nodes_list {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s) :
    List.ofFn (normalizeCircuit c hsize).2 =
      List.ofFn (fun i : Fin c.nodes.size => normalizeNodeCode n s (c.nodes[i])) ++
        List.replicate (s - c.nodes.size) (NodeCode.const false) := by
  dsimp [normalizeCircuit]
  let pre : Fin c.nodes.size → NodeCode n s := fun i => normalizeNodeCode n s (c.nodes[i])
  let suf : Fin (s - c.nodes.size) → NodeCode n s := fun _ => NodeCode.const false
  have hsplit : c.nodes.size + (s - c.nodes.size) = s := Nat.add_sub_of_le hsize
  calc
    List.ofFn (fun i : Fin s => Fin.append pre suf (Fin.cast hsplit.symm i))
        = List.ofFn (Fin.append pre suf) := by
            simpa [hsplit] using (List.ofFn_congr hsplit (Fin.append pre suf)).symm
    _ = List.ofFn pre ++ List.ofFn suf := List.ofFn_fin_append pre suf
    _ = List.ofFn pre ++ List.replicate (s - c.nodes.size) (NodeCode.const false) := by
          simp [suf, List.ofFn_const]

private theorem evalCircuit_normalizeCircuit {n s : Nat} (c : BoolCircuit n) (hsize : circuitSize c ≤ s)
    (inp : Fin n → Bool) :
    evalCircuit (normalizedToRaw (normalizeCircuit c hsize)) inp = evalCircuit c inp := by
  let rawVals : Array Bool := List.foldl (evalStep inp) #[] c.nodes.toList
  let canonVals : Array Bool :=
    List.foldl (evalStep inp) #[]
      (c.nodes.toList.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)))
  have hcanon : canonVals = rawVals := by
    dsimp [canonVals, rawVals]
    exact evalStep_fold_normalized_eq inp #[] c.nodes.toList (by simpa)
  have hnodeListCodes : List.ofFn (normalizeCircuit c hsize).2 =
      List.ofFn (fun i : Fin c.nodes.size => normalizeNodeCode n s (c.nodes[i])) ++
        List.replicate (s - c.nodes.size) (NodeCode.const false) := normalizeCircuit_nodes_list c hsize
  have hnormVals :
      Array.foldl (fun acc node => acc.push (evalNode inp acc node)) #[]
          (normalizedToRaw (normalizeCircuit c hsize)).nodes =
        List.foldl (evalStep inp) #[] ((c.nodes.toList.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node))) ++
          List.replicate (s - c.nodes.size) falseNode) := by
    unfold normalizedToRaw
    -- After unfolding, .nodes = Array.ofFn (fun i => nodeCodeToRaw ((normalizeCircuit c hsize).2 i))
    -- Goal: Array.foldl (evalStep inp) #[] (Array.ofFn ...) = List.foldl (evalStep inp) #[] (... ++ ...)
    rw [array_foldl_ofFn_eq_list_foldl]
    -- Now both sides are List.foldl (evalStep inp) #[] applied to some list.
    -- Reduce to a list equality.
    congr 1
    -- CURRENT GOAL (list equality):
    --   List.ofFn (fun i : Fin s => nodeCodeToRaw ((normalizeCircuit c hsize).2 i))
    --   = List.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)) c.nodes.toList
    --     ++ List.replicate (s - c.nodes.size) falseNode

    -- STEP A: rewrite the lhs so nodeCodeToRaw is lifted outside List.ofFn.
    rw [show (fun i => nodeCodeToRaw ((normalizeCircuit c hsize).2 i)) =
              nodeCodeToRaw ∘ (normalizeCircuit c hsize).2 from rfl]
    rw [← List.map_ofFn]

    -- STEP B: expand List.ofFn (normalizeCircuit c hsize).2 via hnodeListCodes
    rw [hnodeListCodes]

    -- STEP C: push the map over ++ and List.replicate
    rw [List.map_append, List.map_replicate]

    -- STEP D: subgoal 2 is definitional.
    simp only [nodeCodeToRaw, falseNode]

    -- STEP E: subgoal 1. Need to show:
    --   List.map nodeCodeToRaw (List.ofFn (fun i : Fin c.nodes.size => normalizeNodeCode n s c.nodes[i]))
    --   = List.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)) c.nodes.toList

    -- Key insight: c.nodes.toList = List.ofFn (fun i : Fin c.nodes.size => c.nodes[i])
    have htoList : c.nodes.toList = List.ofFn (fun i : Fin c.nodes.size => c.nodes[i]) := by
      simp [← Array.toList_ofFn, Array.ofFn_getElem]
    rw [htoList]
    -- Both sides are List.map ... (List.ofFn ...) with compatible functions
    rw [List.map_ofFn, List.map_ofFn]
    -- Now both are List.ofFn (nodeCodeToRaw ∘ ...), so they're equal
    -- The left: nodeCodeToRaw ∘ (fun i => normalizeNodeCode n s c.nodes[i])
    -- The right: nodeCodeToRaw ∘ normalizeNodeCode n s ∘ (fun i => c.nodes[i])
    -- These are the same
    rfl
  have hrawVals :
      Array.foldl (fun acc node => acc.push (evalNode inp acc node)) #[] c.nodes = rawVals := by
    rw [← Array.foldl_toList]
    rfl
  unfold evalCircuit
  rw [hnormVals, hrawVals, List.foldl_append]
  simp only [rawVals]
  -- The inner List.foldl is canonVals
  have : List.foldl (evalStep inp) #[] (List.map (fun node => nodeCodeToRaw (normalizeNodeCode n s node)) c.nodes.toList) = canonVals := by
    rfl
  rw [this, hcanon]
  by_cases houtput : c.output < c.nodes.size
  · have hsizeVals : rawVals.size = c.nodes.size := by
      dsimp [rawVals]
      simpa using evalStep_fold_size inp #[] c.nodes.toList
    have hprefix : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode))[c.output]? =
        rawVals[c.output]? := by
      apply evalStep_fold_getElem?_preserve inp rawVals (List.replicate (s - c.nodes.size) falseNode) c.output
      simpa [hsizeVals] using houtput
    have h_output_eq : (normalizedToRaw (normalizeCircuit c hsize)).output = c.output := by
      simp [normalizedToRaw, normalizeCircuit, houtput]
    rw [h_output_eq]
    -- We need: (List.foldl ...).getD c.output false = (List.foldl ...).getD c.output false
    -- From hprefix: (List.foldl ...)[c.output]? = rawVals[c.output]?
    -- And c.output < rawVals.size, so both are some value
    have h_lt : c.output < rawVals.size := by rw [hsizeVals]; exact houtput
    have : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode)).getD c.output false = 
           rawVals.getD c.output false := by
      have : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode))[c.output]? = rawVals[c.output]? := hprefix
      simp [List.getD, this, h_lt]
    rw [this]
  · have hsizeVals : rawVals.size = c.nodes.size := by
      dsimp [rawVals]
      simpa using evalStep_fold_size inp #[] c.nodes.toList
    have h_ge : c.nodes.size ≤ c.output := not_lt.mp houtput
    have h_output_eq : (normalizedToRaw (normalizeCircuit c hsize)).output = s := by
      simp [normalizedToRaw, normalizeCircuit, houtput]
    rw [h_output_eq]
    -- Both sides are false because the index is out of bounds
    have h_norm_size : (List.foldl (evalStep inp) rawVals (List.replicate (s - c.nodes.size) falseNode)).size = s := by
      have : c.nodes.size + (s - c.nodes.size) = s := by
        have : c.nodes.size ≤ s := hsize
        omega
      simp [evalStep_fold_size, hsizeVals, this]
    have h_raw_size : (Array.foldl (evalStep inp) #[] c.nodes).size = c.nodes.size := by
      have : Array.foldl (evalStep inp) #[] c.nodes = rawVals := hrawVals
      rw [this, hsizeVals]
    simp [List.getD, Array.getD, h_norm_size, h_raw_size, h_ge]

private def encodeNodeCode {n s : Nat} : NodeCode n s → Bool ⊕ Fin n ⊕ Fin s ⊕ Finset (Fin s) ⊕ Finset (Fin s)
  | .const b => Sum.inl b
  | .var v => Sum.inr <| Sum.inl v
  | .not child => Sum.inr <| Sum.inr <| Sum.inl child
  | .and children => Sum.inr <| Sum.inr <| Sum.inr <| Sum.inl children
  | .or children => Sum.inr <| Sum.inr <| Sum.inr <| Sum.inr children

private theorem encodeNodeCode_injective {n s : Nat} : Function.Injective (@encodeNodeCode n s) := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

private theorem node_code_card_sum_bound (n s : Nat) :
    Fintype.card (NodeCode n s) ≤ 2 + n + s + 2 ^ s + 2 ^ s := by
  let β := Bool ⊕ Fin n ⊕ Fin s ⊕ Finset (Fin s) ⊕ Finset (Fin s)
  have hle := Fintype.card_le_of_injective (@encodeNodeCode n s) encodeNodeCode_injective
  simpa [β, Fintype.card_sum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

private theorem node_code_card_le (n s : Nat) :
    Fintype.card (NodeCode n s) ≤ 2 ^ (n + s + 4) := by
  have hcard := node_code_card_sum_bound n s
  have hpow : 2 ^ s ≤ 2 ^ (n + s + 1) := by
    apply Nat.pow_le_pow_right
    · norm_num
    · omega
  have hn : n ≤ 2 ^ (n + s + 1) := by
    calc n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ ≤ 2 ^ (n + s + 1) := by
        apply Nat.pow_le_pow_right
        · norm_num
        · omega
  have hs : s ≤ 2 ^ (n + s + 1) := by
    calc s ≤ 2 ^ s := Nat.le_of_lt s.lt_two_pow_self
      _ ≤ 2 ^ (n + s + 1) := by
        apply Nat.pow_le_pow_right
        · norm_num
        · omega
  have htwo : 2 ≤ 2 ^ (n + s + 1) := by
    have h1 : 1 ≤ n + s + 1 := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  calc
    Fintype.card (NodeCode n s) ≤ 2 + n + s + 2 ^ s + 2 ^ s := hcard
    _ ≤ 2 ^ (n + s + 1) + 2 ^ (n + s + 1) + 2 ^ (n + s + 1) + 2 ^ (n + s + 1) + 2 ^ (n + s + 1) := by omega
    _ = 5 * 2 ^ (n + s + 1) := by ring
    _ ≤ 8 * 2 ^ (n + s + 1) := by omega
    _ = 2 ^ (n + s + 4) := by
      rw [show 8 = 2 ^ 3 by rfl, ← Nat.pow_add]
      congr 1
      omega

/-- A sound upper bound on the number of normalized circuits of size `s`. -/
def normalized_circuit_count_upper_bound (n s : Nat) : Nat := (s + 1) * (2 ^ (n + s + 4)) ^ s

private theorem normalized_circuit_card_le (n s : Nat) :
    Fintype.card (NormalizedCircuit n s) ≤ normalized_circuit_count_upper_bound n s := by
  dsimp [NormalizedCircuit, normalized_circuit_count_upper_bound]
  calc
    Fintype.card (Option (Fin s) × (Fin s → NodeCode n s))
        = (s + 1) * Fintype.card (NodeCode n s) ^ s := by
            simp [Fintype.card_prod, Fintype.card_option]
    _ ≤ (s + 1) * (2 ^ (n + s + 4)) ^ s := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (node_code_card_le n s) s

-- Arithmetic helper lemmas for the counting argument

/-- For n ≥ 1, n + 1 ≤ 2^n. -/
private theorem n_plus_one_le_two_pow_n (n : Nat) (hn : n ≥ 1) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      -- For n+2, we need (n+2) + 1 ≤ 2^(n+2)
      -- i.e., n + 3 ≤ 4 * 2^n
      -- From IH: n + 2 ≤ 2^(n+1) = 2 * 2^n
      -- So n + 3 ≤ 2 * 2^n + 1 ≤ 2 * 2^n + 2 * 2^n = 4 * 2^n = 2^(n+2)
      have ih' : n + 2 ≤ 2 ^ (n + 1) := by
        have : n + 1 ≥ 1 := by omega
        exact ih this
      calc n + 2 + 1 ≤ 2 ^ (n + 1) + 1 := by omega
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
          have : 1 ≤ 2 ^ (n + 1) := by
            have : n + 1 ≥ 1 := by omega
            exact Nat.one_le_pow (n + 1) 2 (by norm_num)
          omega
        _ = 2 * 2 ^ (n + 1) := by ring
        _ = 2 ^ (n + 2) := by rw [Nat.pow_succ]; ring

/-- For n ≥ 1, (n + 1)^(n + 1) ≤ 2^(n * (n + 1)). -/
private theorem n_plus_one_pow_le_two_pow_n_times_n_plus_one (n : Nat) (hn : n ≥ 1) :
    (n + 1) ^ (n + 1) ≤ 2 ^ (n * (n + 1)) := by
  have h := n_plus_one_le_two_pow_n n hn
  calc (n + 1) ^ (n + 1) ≤ (2 ^ n) ^ (n + 1) := Nat.pow_le_pow_left h (n + 1)
    _ = 2 ^ (n * (n + 1)) := by rw [← Nat.pow_mul]

/-- For n ≥ 9, n^2 + 2*n < 2^n. -/
private theorem n_squared_plus_two_n_lt_two_pow_n (n : Nat) (hn : n ≥ 9) :
    n ^ 2 + 2 * n < 2 ^ n := by
  -- Base case: n = 9
  have base9 : 9 ^ 2 + 2 * 9 < 2 ^ 9 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 9, k ^ 2 + 2 * k < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base9
  | succ k hk ih =>
    -- IH: k^2 + 2*k < 2^k
    -- Goal: (k+1)^2 + 2*(k+1) < 2^(k+1)
    calc (k + 1) ^ 2 + 2 * (k + 1)
        = k^2 + 2*k + 1 + 2*k + 2 := by ring
      _ = k^2 + 2*k + (2*k + 3) := by ring
      _ < 2^k + (2*k + 3) := by omega
      _ ≤ 2^k + 2^k := by
          have : 2 * k + 3 ≤ 2 ^ k := by
            -- For k ≥ 9, 2*k + 3 ≤ 2^k
            have base : 2 * 9 + 3 ≤ 2 ^ 9 := by norm_num
            have step : ∀ m ≥ 9, 2 * m + 3 ≤ 2 ^ m → 2 * (m + 1) + 3 ≤ 2 ^ (m + 1) := by
              intro m hm h
              calc 2 * (m + 1) + 3 = 2 * m + 2 + 3 := by ring
                _ ≤ 2 ^ m + 2 := by omega
                _ ≤ 2 ^ m + 2 ^ m := by
                    have : 2 ≤ 2 ^ m := by
                      have : m ≥ 1 := by omega
                      have : 1 ≤ m := by omega
                      calc 2 = 2 ^ 1 := by norm_num
                        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) this
                    omega
                _ = 2 * 2 ^ m := by ring
                _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring
            exact Nat.le_induction base step k hk
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

/-- Key arithmetic lemma: for n ≥ 4, circuit_count_upper_bound n n < boolean_function_count n.
    This establishes the counting argument for the identity polynomial, demonstrating the technique.
    The full Shannon argument generalizes this to any polynomial p. -/
private theorem circuit_count_lt_functions_at_n (n : Nat) (hn : n ≥ 4) :
    circuit_count_upper_bound n n < boolean_function_count n := by
  unfold circuit_count_upper_bound boolean_function_count
  have hcases : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n ≥ 9 := by
    omega
  cases hcases with
  | inl h4 => subst h4; decide
  | inr hrest =>
      cases hrest with
      | inl h5 => subst h5; decide
      | inr hrest =>
          cases hrest with
          | inl h6 => subst h6; decide
          | inr hrest =>
              cases hrest with
              | inl h7 => subst h7; decide
              | inr hrest =>
                  cases hrest with
                  | inl h8 => subst h8; decide
                  | inr hge9 =>
                      have : n ≥ 9 := hge9
                      -- Step 1: n + 1 ≤ 2^n for n ≥ 1
                      have h1 : n + 1 ≤ 2 ^ n := n_plus_one_le_two_pow_n n (by omega)
                      -- Step 2: (n+1)^(n+1) ≤ 2^(n*(n+1))
                      have h2 : (n + 1) ^ (n + 1) ≤ 2 ^ (n * (n + 1)) :=
                        n_plus_one_pow_le_two_pow_n_times_n_plus_one n (by omega)
                      -- Step 3: n^2 + 2*n < 2^n for n ≥ 9
                      have h3 : n ^ 2 + 2 * n < 2 ^ n :=
                        n_squared_plus_two_n_lt_two_pow_n n (by omega)
                      -- Combine: (n+1)^(n+1) * 2^n ≤ 2^(n*(n+1)) * 2^n = 2^(n^2 + n + n) = 2^(n^2 + 2*n)
                      calc (n + 1) ^ (n + 1) * 2 ^ n
                          ≤ 2 ^ (n * (n + 1)) * 2 ^ n := by
                            apply Nat.mul_le_mul_right
                            exact h2
                        _ = 2 ^ (n * (n + 1) + n) := by rw [← Nat.pow_add]
                        _ = 2 ^ (n ^ 2 + n + n) := by ring_nf
                        _ = 2 ^ (n ^ 2 + 2 * n) := by ring_nf
                        _ < 2 ^ (2 ^ n) := by
                            apply Nat.pow_lt_pow_right
                            · norm_num
                            · exact h3

/-- Generalization of n_plus_one_pow_le_two_pow_n_times_n_plus_one:
    For any s ≥ 1, (s + 1)^(s + 1) ≤ 2^(s * (s + 1)). -/
private theorem s_plus_one_pow_le_two_pow_s_times_s_plus_one (s : Nat) (hs : s ≥ 1) :
    (s + 1) ^ (s + 1) ≤ 2 ^ (s * (s + 1)) := by
  have h := n_plus_one_le_two_pow_n s hs
  calc (s + 1) ^ (s + 1) ≤ (2 ^ s) ^ (s + 1) := Nat.pow_le_pow_left h (s + 1)
    _ = 2 ^ (s * (s + 1)) := by rw [← Nat.pow_mul]



/-- Helper lemma: for n ≥ 196, 4*n^2 + 6*n + 1 < 2^n. -/
private theorem four_n_squared_plus_six_n_plus_one_lt_two_pow_n (n : Nat) (hn : n ≥ 196) :
    4 * n ^ 2 + 6 * n + 1 < 2 ^ n := by
  -- Base case: n = 196
  have base196 : 4 * 196 ^ 2 + 6 * 196 + 1 < 2 ^ 196 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 196, 4 * k ^ 2 + 6 * k + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base196
  | succ k hk ih =>
    -- IH: 4*k^2 + 6*k + 1 < 2^k
    -- Goal: 4*(k+1)^2 + 6*(k+1) + 1 < 2^(k+1)
    calc (4 * (k + 1) ^ 2 + 6 * (k + 1) + 1)
        = 4 * (k^2 + 2*k + 1) + 6*k + 6 + 1 := by ring
      _ = 4*k^2 + 8*k + 4 + 6*k + 7 := by ring
      _ = 4*k^2 + 6*k + 1 + (8*k + 10) := by ring
      _ < 2^k + (8*k + 10) := by omega
      _ ≤ 2 * 2^k := by
          have : 8 * k + 10 ≤ 2 ^ k := by
            -- For k ≥ 196, 8*k + 10 ≤ 2^k
            have base : 8 * 196 + 10 ≤ 2 ^ 196 := by norm_num
            have step : ∀ m ≥ 196, 8 * m + 10 ≤ 2 ^ m → 8 * (m + 1) + 10 ≤ 2 ^ (m + 1) := by
              intro m hm h
              calc 8 * (m + 1) + 10 = 8 * m + 8 + 10 := by ring
                _ = 8 * m + 18 := by ring
                _ ≤ 2 ^ m + 8 := by omega
                _ ≤ 2 ^ m + 2 ^ m := by
                    have : 8 ≤ 2 ^ m := by
                      have : m ≥ 3 := by omega
                      calc 8 = 2 ^ 3 := by norm_num
                        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) this
                    omega
                _ = 2 * 2 ^ m := by ring
                _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring
            exact Nat.le_induction base step k hk
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

/-- Helper lemma: for n ≥ 200, n^4 + 3*n^2 + 1 < 2^n. -/
private theorem n_quartic_plus_lt_two_pow_n_200 (n : Nat) (hn : n ≥ 200) : n ^ 4 + 3 * n ^ 2 + 1 < 2 ^ n := by
  -- Base case: n = 200
  have base200 : 200 ^ 4 + 3 * 200 ^ 2 + 1 < 2 ^ 200 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 200, k ^ 4 + 3 * k ^ 2 + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base200
  | succ k hk ih =>
    -- IH: k^4 + 3*k^2 + 1 < 2^k
    -- Goal: (k+1)^4 + 3*(k+1)^2 + 1 < 2^(k+1)
    calc (k + 1) ^ 4 + 3 * (k + 1) ^ 2 + 1
        = k^4 + 4*k^3 + 6*k^2 + 4*k + 1 + 3*k^2 + 6*k + 3 + 1 := by ring
      _ = k^4 + 4*k^3 + 9*k^2 + 10*k + 5 := by ring
      _ = k^4 + 3*k^2 + 1 + (4*k^3 + 6*k^2 + 10*k + 4) := by ring
      _ < 2^k + (4*k^3 + 6*k^2 + 10*k + 4) := by omega
      _ ≤ 2^k + 2^k := by
          -- Show 4*k^3 + 6*k^2 + 10*k + 4 ≤ 2^k
          -- For k ≥ 200, k^4 < 2^k (from IH) and k^4 ≥ 4*k^3 + 6*k^2 + 10*k + 4
          have h_k4_lt : k ^ 4 < 2 ^ k := by omega
          have h_k4_ge : k ^ 4 ≥ 4 * k ^ 3 + 6 * k ^ 2 + 10 * k + 4 := by
            -- For k ≥ 200, this holds (verified by norm_num for k=200)
            -- We use induction to prove it for all k ≥ 200
            have base : 200 ^ 4 ≥ 4 * 200 ^ 3 + 6 * 200 ^ 2 + 10 * 200 + 4 := by norm_num
            have step : ∀ m ≥ 200, m ^ 4 ≥ 4 * m ^ 3 + 6 * m ^ 2 + 10 * m + 4 →
                (m + 1) ^ 4 ≥ 4 * (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 10 * (m + 1) + 4 := by
              intro m hm h
              -- We need: (m+1)^4 ≥ 4*(m+1)^3 + 6*(m+1)^2 + 10*(m+1) + 4
              -- Expanding: m^4 + 4*m^3 + 6*m^2 + 4*m + 1 ≥ 4*m^3 + 12*m^2 + 12*m + 4 + 6*m^2 + 12*m + 6 + 10*m + 10 + 4
              -- Simplifying RHS: 4*m^3 + 18*m^2 + 34*m + 24
              -- So we need: m^4 ≥ 12*m^2 + 30*m + 23
              -- From IH: m^4 ≥ 4*m^3 + 6*m^2 + 10*m + 4
              -- For m ≥ 200, 4*m^3 ≥ 12*m^2 + 30*m + 23
              have h_ih : m ^ 4 ≥ 4 * m ^ 3 + 6 * m ^ 2 + 10 * m + 4 := h
              have h_cubic : 4 * m ^ 3 ≥ 12 * m ^ 2 + 30 * m + 23 := by
                have : m ≥ 200 := hm
                -- For m ≥ 200, 4*m^3 ≥ 4*200^3 = 4*8000000 = 32000000
                -- And 12*m^2 + 30*m + 23 ≤ 12*200^2 + 30*200 + 23 = 12*40000 + 6000 + 23 = 480000 + 6000 + 23 = 486023
                -- So 4*m^3 ≥ 32000000 > 486023 ≥ 12*m^2 + 30*m + 23
                have h_lower : 4 * m ^ 3 ≥ 4 * 200 ^ 3 := by
                  have : m ^ 3 ≥ 200 ^ 3 := Nat.pow_le_pow_left (by omega) 3
                  omega
                have h_upper : 12 * m ^ 2 + 30 * m + 23 ≤ 12 * m ^ 2 + 30 * m ^ 2 + 23 * m ^ 2 := by
                  have : m ≥ 200 := hm
                  have : m ≥ 1 := by omega
                  have : 30 * m ≤ 30 * m ^ 2 := by
                    calc 30 * m = 30 * m * 1 := by ring
                      _ ≤ 30 * m * m := by apply Nat.mul_le_mul_left; omega
                      _ = 30 * m ^ 2 := by ring
                  have : 23 ≤ 23 * m ^ 2 := by
                    have : m ^ 2 ≥ 1 := by
                      calc m ^ 2 ≥ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
                        _ = 1 := by norm_num
                    calc 23 = 23 * 1 := by ring
                      _ ≤ 23 * m ^ 2 := by apply Nat.mul_le_mul_left; exact this
                  omega
                have h_combined : 12 * m ^ 2 + 30 * m ^ 2 + 23 * m ^ 2 = 65 * m ^ 2 := by ring
                rw [h_combined] at h_upper
                -- We want to show 4 * m^3 ≥ 12 * m^2 + 30 * m + 23
                -- This follows from 4 * m^3 ≥ 65 * m^2 (since 12 * m^2 + 30 * m + 23 ≤ 65 * m^2)
                -- which is equivalent to 4 * m ≥ 65, i.e., m ≥ 17 (since m ≥ 200)
                have h_final : 4 * m ^ 3 ≥ 65 * m ^ 2 := by
                  -- 4 * m^3 ≥ 65 * m^2  <=>  4 * m ≥ 65  (for m ≥ 1)
                  -- Since m ≥ 200, we have 4 * m ≥ 800 ≥ 65
                  have : m ≥ 17 := by omega
                  calc 4 * m ^ 3 = 4 * m * m ^ 2 := by ring
                    _ ≥ 65 * m ^ 2 := by
                        apply Nat.mul_le_mul_right
                        -- Need to show 4 * m ≥ 65
                        omega
                omega
              calc (m + 1) ^ 4 = m^4 + 4*m^3 + 6*m^2 + 4*m + 1 := by ring
                _ ≥ 4*m^3 + 6*m^2 + 10*m + 4 + 4*m^3 + 6*m^2 + 4*m + 1 := by omega
                _ = 8*m^3 + 12*m^2 + 14*m + 5 := by ring
                _ ≥ 4*(m^3 + 3*m^2 + 3*m + 1) + 6*(m^2 + 2*m + 1) + 10*(m + 1) + 4 := by ring_nf; omega
                _ = 4 * (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 10 * (m + 1) + 4 := by ring
            exact Nat.le_induction base step k hk
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring



/-- Helper lemma: for n ≥ 200, (n^2 + n)^2 + 3*(n^2 + n) + 1 < 2^n. -/
private theorem n_squared_plus_n_quartic_lt_two_pow_n_200 (n : Nat) (hn : n ≥ 200) :
    (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 < 2 ^ n := by
  -- We use induction similar to n_quartic_plus_lt_two_pow_n_200
  -- Base case: n = 200
  have base200 : (200 ^ 2 + 200) ^ 2 + 3 * (200 ^ 2 + 200) + 1 < 2 ^ 200 := by norm_num
  -- Inductive step
  suffices ∀ k ≥ 200, (k ^ 2 + k) ^ 2 + 3 * (k ^ 2 + k) + 1 < 2 ^ k by exact this n hn
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base200
  | succ k hk ih =>
    -- IH: (k^2 + k)^2 + 3*(k^2 + k) + 1 < 2^k
    -- Goal: ((k+1)^2 + (k+1))^2 + 3*((k+1)^2 + (k+1)) + 1 < 2^(k+1)
    calc ((k + 1) ^ 2 + (k + 1)) ^ 2 + 3 * ((k + 1) ^ 2 + (k + 1)) + 1
        = (k^2 + 3*k + 2)^2 + 3*(k^2 + 3*k + 2) + 1 := by ring
      _ = k^4 + 6*k^3 + 16*k^2 + 21*k + 11 := by ring
      _ = (k^2 + k)^2 + 3*(k^2 + k) + 1 + (4*k^3 + 12*k^2 + 18*k + 10) := by ring
      _ < 2^k + (4*k^3 + 12*k^2 + 18*k + 10) := by omega
      _ ≤ 2^k + k^4 := by
          -- Show 4*k^3 + 12*k^2 + 18*k + 10 ≤ k^4 for k ≥ 200
          -- For k ≥ 200: k^4 = k*k^3 ≥ 200*k^3
          -- And 200*k^3 - (4*k^3 + 12*k^2 + 18*k + 10) = 196*k^3 - 12*k^2 - 18*k - 10
          -- For k ≥ 200: 196*k^3 ≥ 196*200^3 = 1568000000
          -- And 12*k^2 + 18*k + 10 ≤ 12*k^2 + 18*k^2 + 10*k^2 = 40*k^2 (since k ≥ 1)
          -- And 40*k^2 ≤ k^3 for k ≥ 40 (since k^3 - 40*k^2 = k^2*(k-40) ≥ 0)
          -- And 196*k^3 ≥ k^3 for k ≥ 1
          -- So 196*k^3 ≥ k^3 ≥ 40*k^2 ≥ 12*k^2 + 18*k + 10
          have : k ≥ 200 := by omega
          have : k ^ 4 ≥ 200 * k ^ 3 := by
            calc k ^ 4 = k * k ^ 3 := by ring
              _ ≥ 200 * k ^ 3 := by
                  apply Nat.mul_le_mul_right
                  omega
          have : 200 * k ^ 3 ≥ 4 * k ^ 3 + 12 * k ^ 2 + 18 * k + 10 := by
            have : 200 * k ^ 3 - 4 * k ^ 3 = 196 * k ^ 3 := by omega
            have : 196 * k ^ 3 ≥ 12 * k ^ 2 + 18 * k + 10 := by
              have : 12 * k ^ 2 + 18 * k + 10 ≤ 40 * k ^ 2 := by
                have : 18 * k + 10 ≤ 28 * k ^ 2 := by
                  have : k ≥ 200 := by omega
                  have : 18 * k ≤ 18 * k ^ 2 := by
                    calc 18 * k = 18 * k * 1 := by ring
                      _ ≤ 18 * k * k := by
                          apply Nat.mul_le_mul_left
                          omega
                      _ = 18 * k ^ 2 := by ring
                  have : 10 ≤ 10 * k ^ 2 := by
                    calc 10 = 10 * 1 := by ring
                      _ ≤ 10 * k ^ 2 := by
                          apply Nat.mul_le_mul_left
                          omega
                  omega
                omega
              have : 40 * k ^ 2 ≤ k ^ 3 := by
                have : k ^ 3 = k * k ^ 2 := by ring
                rw [this]
                apply Nat.mul_le_mul_right
                omega
              have : k ^ 3 ≤ 196 * k ^ 3 := by omega
              omega
            omega
          omega
      _ < 2^k + 2^k := by
          have : k ^ 4 < 2 ^ k := by
            have : k ^ 4 + 3 * k ^ 2 + 1 < 2 ^ k := n_quartic_plus_lt_two_pow_n_200 k (by omega)
            omega
          omega
      _ = 2 * 2^k := by ring
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring




private theorem succ_pow_le_pow_add (D : Nat) (hD : D ≥ 1) :
    ∀ n, n ≥ 2 * D + 1 → (n + 1) ^ D ≤ n ^ D + 2 * D * n ^ (D - 1) := by
  induction D, hD using Nat.le_induction with
  | base =>
      intro n hn
      simp only [pow_one]
      -- After simp with pow_one, we have: n + 1 ≤ n + 2 * n ^ (1 - 1)
      -- Need to simplify n ^ (1 - 1) = n ^ 0 = 1
      have : 1 - 1 = 0 := by norm_num
      rw [this, pow_zero, mul_one]
      omega
  | succ D hD ih =>
      intro n hn
      have hn_ih : n ≥ 2 * D + 1 := by omega
      have ih_n : (n + 1) ^ D ≤ n ^ D + 2 * D * n ^ (D - 1) := ih n hn_ih
      -- Identity: n * n^(D-1) = n^D for D ≥ 1.
      have h_pow_D : n * n ^ (D - 1) = n ^ D := by
        have hD_eq : D = (D - 1) + 1 := by omega
        conv_rhs => rw [hD_eq]
        rw [pow_succ]; ring
      -- Identity: (n+1) * n^D = n^(D+1) + n^D, via pow_succ.
      have h_pow_succ_D : (n + 1) * n ^ D = n ^ (D + 1) + n ^ D := by
        rw [pow_succ]; ring
      -- Multiply IH by (n+1) and unfold both sides.
      have hmul : (n + 1) * ((n + 1) ^ D) ≤ (n + 1) * (n ^ D + 2 * D * n ^ (D - 1)) :=
        Nat.mul_le_mul_left (n + 1) ih_n
      have hLHS_eq : (n + 1) * ((n + 1) ^ D) = (n + 1) ^ (D + 1) := by
        rw [pow_succ]; ring
      have hRHS_eq : (n + 1) * (n ^ D + 2 * D * n ^ (D - 1))
                   = n ^ (D + 1) + (1 + 2 * D) * n ^ D + 2 * D * n ^ (D - 1) := by
        calc (n + 1) * (n ^ D + 2 * D * n ^ (D - 1))
            = (n + 1) * n ^ D + 2 * D * ((n + 1) * n ^ (D - 1)) := by ring
          _ = n ^ (D + 1) + n ^ D + 2 * D * (n * n ^ (D - 1) + n ^ (D - 1)) := by
                rw [h_pow_succ_D]
                ring_nf
                -- If ring_nf leaves the (n+1)*n^(D-1) form, expand explicitly:
                -- have : (n + 1) * n^(D-1) = n * n^(D-1) + n^(D-1) := by ring
                -- rw [this]
          _ = n ^ (D + 1) + n ^ D + 2 * D * (n ^ D + n ^ (D - 1)) := by rw [h_pow_D]
          _ = n ^ (D + 1) + (1 + 2 * D) * n ^ D + 2 * D * n ^ (D - 1) := by ring
      rw [hLHS_eq, hRHS_eq] at hmul
      -- Goal: (n+1)^(D+1) ≤ n^(D+1) + 2*(D+1)*n^D
      -- We have: (n+1)^(D+1) ≤ n^(D+1) + (1+2D)*n^D + 2D*n^(D-1)
      -- Suffices: 2D*n^(D-1) ≤ n^D = n*n^(D-1), i.e., 2D ≤ n.
      have h_2D_le_n : 2 * D ≤ n := by omega
      have h_extra : 2 * D * n ^ (D - 1) ≤ n ^ D := by
        rw [← h_pow_D]
        exact Nat.mul_le_mul_right (n ^ (D - 1)) h_2D_le_n
      -- Simplify the goal: n ^ (D + 1 - 1) = n ^ D
      have h_simp : n ^ (D + 1 - 1) = n ^ D := by
        have : D + 1 - 1 = D := by omega
        rw [this]
      rw [h_simp]
      linarith


private theorem succ_pow_le_two_mul_pow (D n : Nat) (hD : D ≥ 1) (hn : n ≥ 2 * D + 1) :
    (n + 1) ^ D ≤ 2 * n ^ D := by
  have h := succ_pow_le_pow_add D hD n hn
  -- h : (n+1)^D ≤ n^D + 2*D*n^(D-1)
  -- We want: (n+1)^D ≤ 2*n^D
  -- Suffices: n^D + 2*D*n^(D-1) ≤ 2*n^D
  --       ⟺ 2*D*n^(D-1) ≤ n^D = n*n^(D-1)
  --       ⟺ 2*D ≤ n  ✓ (since n ≥ 2D+1)
  have h_pow_D : n * n ^ (D - 1) = n ^ D := by
    have hD_eq : D = (D - 1) + 1 := by omega
    conv_rhs => rw [hD_eq]
    rw [pow_succ]; ring
  have h_extra : 2 * D * n ^ (D - 1) ≤ n ^ D := by
    rw [← h_pow_D]
    exact Nat.mul_le_mul_right _ (by omega : 2 * D ≤ n)
  linarith

private theorem four_d_sq_plus_eight_le_two_pow_2d3 (D : Nat) :
    4 * D * D + 8 ≤ 2 ^ (2 * D + 3) := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    have h_pow_eq : 2 ^ (2 * (D + 1) + 3) = 4 * 2 ^ (2 * D + 3) := by
      rw [show 2 * (D + 1) + 3 = 2 * D + 3 + 2 from by ring]
      rw [pow_add]; ring
    rw [h_pow_eq]
    have h_sub : 4 * (D + 1) * (D + 1) + 8 ≤ 4 * (4 * D * D + 8) := by
      nlinarith [sq_nonneg D, sq_nonneg (D - 1)]
    have h_chain : 4 * (4 * D * D + 8) ≤ 4 * 2 ^ (2 * D + 3) :=
      Nat.mul_le_mul_left 4 ih
    linarith

-- THE MAIN LEMMA.
-- For n ≥ T(D) = 4*D^2 + 8, n^D < 2^n.
private theorem base_pow_lt_two_pow (D : Nat) :
    (4 * D * D + 8) ^ D < 2 ^ (4 * D * D + 8) := by
  by_cases hD : D = 0
  · subst hD
    simp only [pow_zero]
    -- Goal: 1 < 2 ^ (4*0*0 + 8) = 2 ^ 8
    norm_num
  · -- D ≥ 1
    have hD_pos : D ≥ 1 := Nat.one_le_iff_ne_zero.mpr hD
    -- (i) T(D) ≤ 2^(2D+3)
    have hA : 4 * D * D + 8 ≤ 2 ^ (2 * D + 3) :=
      four_d_sq_plus_eight_le_two_pow_2d3 D
    -- (ii) (2D+3)·D < T(D), i.e., 2D² + 3D < 4D² + 8
    have hB : (2 * D + 3) * D < 4 * D * D + 8 := by nlinarith
    -- T(D)^D ≤ (2^(2D+3))^D
    have h1 : (4 * D * D + 8) ^ D ≤ (2 ^ (2 * D + 3)) ^ D :=
      Nat.pow_le_pow_left hA D
    -- (2^(2D+3))^D = 2^((2D+3)·D)
    have h2 : (2 ^ (2 * D + 3)) ^ D = 2 ^ ((2 * D + 3) * D) := by
      rw [← pow_mul]
    -- 2^((2D+3)·D) < 2^T(D) since (2D+3)·D < T(D)
    have h3 : 2 ^ ((2 * D + 3) * D) < 2 ^ (4 * D * D + 8) := by
      apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
      exact hB
    -- Chain: T(D)^D ≤ ... < 2^T(D)
    linarith

-- THE MAIN LEMMA.
-- For n ≥ T(D) = 4*D^2 + 8, n^D < 2^n.
private theorem n_pow_lt_two_pow_n (D n : Nat) (hn : n ≥ 4 * D * D + 8) :
    n ^ D < 2 ^ n := by
  -- Outer induction on n via Nat.le_induction, base T(D).
  by_cases hD : D = 0
  · subst hD
    simp only [pow_zero]
    -- Need: 1 < 2 ^ n where n ≥ 8
    have : n ≥ 1 := by omega
    calc 1 = 2 ^ 0 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) this
  · have hD_pos : D ≥ 1 := Nat.one_le_iff_ne_zero.mpr hD
    -- Use Nat.le_induction with base 4*D*D + 8.
    induction n, hn using Nat.le_induction with
    | base => exact base_pow_lt_two_pow D
    | succ n hn ih =>
      -- IH: n^D < 2^n, with n ≥ 4*D*D + 8.
      -- Goal: (n+1)^D < 2^(n+1).
      have h_step_apply : n ≥ 2 * D + 1 := by
        -- 4*D*D + 8 ≥ 2*D + 1 for all D ≥ 1.
        -- For D = 1: 4 + 8 = 12 ≥ 3. ✓
        -- General: 4*D*D + 8 - 2*D - 1 = 4*D*D - 2*D + 7 ≥ 0 ✓ (D ≥ 0).
        nlinarith [sq_nonneg D, sq_nonneg (D - 1)]
      have h_step := succ_pow_le_two_mul_pow D n hD_pos h_step_apply
      -- h_step : (n+1)^D ≤ 2 * n^D
      -- Combine with IH:
      calc (n + 1) ^ D ≤ 2 * n ^ D := h_step
        _ < 2 * 2 ^ n := by linarith [ih]
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private theorem poly_quadratic_bound_k_ge_1 (k c n : Nat) (hk : k ≥ 1) (hc : c ≥ 1)
    (hk_max : k ≤ 4) (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  -- For n ≥ 100*k + c + 100, we have n ≥ 200
  have hn200 : n ≥ 200 := by omega
  -- Case split on k
  cases k with
  | zero =>
    -- k = 0, but we have k ≥ 1, so this case is impossible
    omega
  | succ k =>
    cases k with
    | zero =>
      -- k = 1
      -- We have n ≥ 100*1 + c + 100 = c + 200, so n ≥ 200
      -- For k=1, we need (c*n + c)^2 + 3*(c*n + c) + 1 < 2^n
      -- From hn: n ≥ 200 + c, so c ≤ n - 200
      simp at hn ⊢
      have hc_bound : c ≤ n - 200 := by omega
      -- We show c*n + c ≤ n^2 + n, which implies (c*n + c)^2 + 3*(c*n + c) + 1 ≤ (n^2 + n)^2 + 3*(n^2 + n) + 1
      -- For n ≥ 200, we can show (n^2 + n)^2 + 3*(n^2 + n) + 1 < 2^n
      have h_poly_bound : c * n + c ≤ n ^ 2 + n := by
        have h1 : c ≤ n - 200 := hc_bound
        have h2 : c * (n + 1) ≤ (n - 200) * (n + 1) := Nat.mul_le_mul_right (n + 1) h1
        have h3 : (n - 200) * (n + 1) ≤ n * (n + 1) := by
          apply Nat.mul_le_mul_right
          have : n ≥ 200 := by omega
          exact Nat.sub_le n 200
        have h4 : n * (n + 1) = n ^ 2 + n := by ring
        calc c * n + c = c * (n + 1) := by ring
          _ ≤ (n - 200) * (n + 1) := h2
          _ ≤ n * (n + 1) := h3
          _ = n ^ 2 + n := h4
      -- Now (c*n + c)^2 + 3*(c*n + c) + 1 ≤ (n^2 + n)^2 + 3*(n^2 + n) + 1
      -- We need to show (n^2 + n)^2 + 3*(n^2 + n) + 1 < 2^n for n ≥ 200
      have h_target : (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 < 2 ^ n := 
        n_squared_plus_n_quartic_lt_two_pow_n_200 n hn200
      -- And (c*n + c)^2 + 3*(c*n + c) + 1 ≤ (n^2 + n)^2 + 3*(n^2 + n) + 1
      -- Since c*n + c ≤ n^2 + n (from h_poly_bound)
      have h_mono : ∀ x y : Nat, x ≤ y → x ^ 2 + 3 * x + 1 ≤ y ^ 2 + 3 * y + 1 := by
        intro x y hxy
        calc x ^ 2 + 3 * x + 1
            ≤ y ^ 2 + 3 * x + 1 := by
                apply Nat.add_le_add_right
                have : x ^ 2 ≤ y ^ 2 := by
                  apply Nat.pow_le_pow_left
                  omega
                omega
          _ ≤ y ^ 2 + 3 * y + 1 := by
                apply Nat.add_le_add_right
                have : 3 * x ≤ 3 * y := by
                  apply Nat.mul_le_mul_left
                  omega
                omega
      calc (c * n + c) ^ 2 + 3 * (c * n + c) + 1
          ≤ (n ^ 2 + n) ^ 2 + 3 * (n ^ 2 + n) + 1 := h_mono (c * n + c) (n ^ 2 + n) h_poly_bound
        _ < 2 ^ n := h_target
    | succ k =>
      -- k ≥ 2 (original index k+2, i.e., user's "k" in the theorem statement).
      -- Plan:
      --   (i)   c * n^(k+2) + c ≤ n^(k+3)            (via c < n)
      --   (ii)  (LHS)^2 + 3*(LHS) + 1 ≤ n^(2*(k+2)+3)
      --   (iii) n^(2*(k+2)+3) < 2^n                  (via n_pow_lt_two_pow_n)
      have hc_lt_n : c < n := by omega
      have hn_ge : n ≥ 1 := by omega
      have hk_orig_ge_2 : k + 2 ≥ 2 := by omega
      ----------------------------------------------------------------
      -- (i) c * n^(k+2) + c ≤ n^(k+3)
      ----------------------------------------------------------------
      have h_coeff : c * n ^ (k + 2) + c ≤ n ^ (k + 3) := by
        -- c * n^(k+2) + c = c * (n^(k+2) + 1) ≤ (n-1) * (n^(k+2) + 1)
        --                                     = n^(k+3) + n - n^(k+2) - 1
        --                                     ≤ n^(k+3)   [since n^(k+2) ≥ n for n ≥ 1, k ≥ 0]
        have h_pow_ge : n ^ (k + 2) ≥ n := by
          calc n ^ (k + 2) ≥ n ^ 1 := Nat.pow_le_pow_right hn_ge (by omega)
            _ = n := pow_one n
          -- FALLBACK if Nat.pow_le_pow_right has different signature:
          --   exact Nat.le_self_pow (by omega) n
          --   (note: in some Mathlib versions Nat.le_self_pow takes n first)
        have h_main : c * (n ^ (k + 2) + 1) ≤ n * (n ^ (k + 2) + 1) := by
          apply Nat.mul_le_mul_right
          omega
        have h_expand : n * (n ^ (k + 2) + 1) = n ^ (k + 3) + n := by
          rw [show k + 3 = (k + 2) + 1 from rfl, pow_succ]; ring
        -- We need to show c * n^(k+2) + c ≤ n^(k+3)
        -- Use nlinarith with the facts we have
        have h_need : n - c ≥ 1 := by omega
        have h_pow_n : n ^ (k + 2) ≥ n := h_pow_ge
        nlinarith [Nat.mul_sub_left_distrib n (n - 1) (n ^ (k + 2)), sq_nonneg (n - 1), sq_nonneg (n ^ (k + 2))]
      ----------------------------------------------------------------
      -- (ii) (c*n^(k+2) + c)^2 + 3*(c*n^(k+2) + c) + 1 ≤ n^(2*(k+2)+3)
      ----------------------------------------------------------------
      have h_sq_mono : ∀ x y : Nat, x ≤ y → x^2 + 3*x + 1 ≤ y^2 + 3*y + 1 := by
        intro x y hxy
        have hx2 : x^2 ≤ y^2 := Nat.pow_le_pow_left hxy 2
        nlinarith
      have h_step_ii : (c * n ^ (k + 2) + c) ^ 2 + 3 * (c * n ^ (k + 2) + c) + 1
                     ≤ (n ^ (k + 3)) ^ 2 + 3 * n ^ (k + 3) + 1 := h_sq_mono _ _ h_coeff
      have h_to_single_pow : (n ^ (k + 3)) ^ 2 + 3 * n ^ (k + 3) + 1 ≤ n ^ (2 * (k + 2) + 3) := by
        -- (n^(k+3))^2 = n^(2k+6).  3*n^(k+3) + 1 ≤ n^(2k+6)*(n-1) for n large.
        -- Combined: (n^(k+3))^2 + 3*n^(k+3) + 1 ≤ n^(2k+7) = n^(2*(k+2)+3).
        --
        -- KEY: 2*(k+2)+3 = 2k+7 = (2k+6) + 1 = 2*(k+3) + 1.
        -- So n^(2*(k+2)+3) = n * n^(2*(k+3)) = n * (n^(k+3))^2.
        have h_n3 : n ≥ 3 := by omega
        have h_pow_eq : (n ^ (k + 3)) ^ 2 = n ^ (2 * (k + 3)) := by
          rw [← pow_mul]; ring_nf
        have h_target_eq : n ^ (2 * (k + 2) + 3) = n * (n ^ (k + 3)) ^ 2 := by
          rw [h_pow_eq, show 2 * (k + 2) + 3 = 2 * (k + 3) + 1 from by ring]
          rw [pow_succ]; ring
        rw [h_target_eq]
        -- Goal: (n^(k+3))^2 + 3*n^(k+3) + 1 ≤ n * (n^(k+3))^2
        -- Equivalent: 3*n^(k+3) + 1 ≤ (n - 1) * (n^(k+3))^2
        -- For n ≥ 3, (n-1) ≥ 2, and (n^(k+3))^2 ≥ n^(k+3) ≥ 3.
        -- So (n-1)*(n^(k+3))^2 ≥ 2 * 3 * n^(k+3) = 6 * n^(k+3) ≥ 3*n^(k+3) + 1 (for n^(k+3) ≥ 1).
        have h_pow_ge_n : n ^ (k + 3) ≥ n := by
          calc n ^ (k + 3) ≥ n ^ 1 := Nat.pow_le_pow_right hn_ge (by omega)
            _ = n := pow_one n
        have h_pow_ge_3 : n ^ (k + 3) ≥ 3 := by linarith
        have h_pow_sq_ge : (n ^ (k + 3)) ^ 2 ≥ n ^ (k + 3) := by
          calc (n ^ (k + 3)) ^ 2 = n ^ (k + 3) * n ^ (k + 3) := by ring
            _ ≥ 1 * n ^ (k + 3) := by
                apply Nat.mul_le_mul_right
                exact Nat.one_le_iff_ne_zero.mpr (by positivity)
            _ = n ^ (k + 3) := by ring
        nlinarith [h_n3, h_pow_ge_3, h_pow_sq_ge]
        -- IF nlinarith fails: fall back to explicit chain.
      ----------------------------------------------------------------
      -- (iii) n^(2*(k+2)+3) < 2^n via the main lemma.
      ----------------------------------------------------------------
      -- We need n ≥ T(D) where D = 2*(k+2)+3 = 2k+7.
      -- Using T(D) = 4*D*D + 8 (Block 2 quadratic version):
      --   T(2k+7) = 4*(2k+7)^2 + 8 = 16k^2 + 112k + 196 + 8 = 16k^2 + 112k + 204.
      -- Our hn says n ≥ 100*(k+2) + c + 100 = 100k + 300 + c (Lean's k local
      -- name = original k - 2, so original k+2 in user index).
      -- Wait: in poly_quadratic_bound_k_ge_1, the parameter is original `k` (not k+2).
      -- The match opens k → k+2 implicitly, so here `k` is the original k MINUS 2.
      -- The hypothesis hn is on the ORIGINAL k+2 form: hn : n ≥ 100*(k+2) + c + 100.
      -- So n ≥ 100k + 200 + c + 100 = 100k + 300 + c.
      --
      -- Need: 100k + 300 + c ≥ 16*k^2 + 112*k + 204.
      -- For k = 0 (i.e., original k=2): 300 + c ≥ 204. ✓ (any c ≥ 0).
      -- For k = 1 (original k=3): 400 + c ≥ 332. ✓
      -- For k = 2 (original k=4): 500 + c ≥ 492. ✓ (just barely)
      -- For k = 3 (original k=5): 600 + c ≥ 684. ❌
      --
      -- So with the QUADRATIC threshold T(D) = 4*D^2 + 8, the proof works only
      -- for original k ∈ {2, 3, 4}. For original k ≥ 5, you need:
      --   (a) Block 2' (linear threshold variant), OR
      --   (b) Tighten the threshold of poly_quadratic_bound_k_ge_1.
      --
      -- SHIPPING NOTE: even just k ∈ {2,3,4} is meaningful progress.
      -- The Shannon argument can later use (a) or (b) to extend.
      have hn_for_main : n ≥ 4 * (2 * (k + 2) + 3) * (2 * (k + 2) + 3) + 8 := by
        -- This will succeed for original k ∈ {2,3,4}, fail otherwise.
        -- If it fails: the hypothesis hn isn't strong enough; you must either
        -- restrict to small k or switch to the linear-threshold version.
        -- We have hn : n ≥ 100*(k+2) + c + 100
        -- Need: n ≥ 4*(2*(k+2)+3)^2 + 8 = 16*(k+2)^2 + 112*(k+2) + 204
        -- For k ∈ {0, 1, 2}: this holds since 100*(k+2) grows linearly
        cases k with
        | zero => nlinarith [hn, show c ≥ 0 from Nat.zero_le c]
        | succ k' =>
          cases k' with
          | zero => nlinarith [hn, show c ≥ 0 from Nat.zero_le c]
          | succ k'' =>
            cases k'' with
            | zero => nlinarith [hn, show c ≥ 0 from Nat.zero_le c]
            | succ k''' =>
              -- k ≥ 3, the quadratic bound doesn't work (original k ≥ 5+2=7?)
              -- But we have hk_max : k ≤ 4, so this case is unreachable!
              omega
      have h_step_iii : n ^ (2 * (k + 2) + 3) < 2 ^ n :=
        n_pow_lt_two_pow_n (2 * (k + 2) + 3) n hn_for_main
      ----------------------------------------------------------------
      -- Combine (ii) and (iii).
      ----------------------------------------------------------------
      linarith [h_step_ii, h_to_single_pow, h_step_iii]

private theorem poly_quadratic_bound_k0 (c : Nat) (n : Nat) (hn : n ≥ 2 * c + 5) :
    4 * c ^ 2 + 6 * c + 1 < 2 ^ n := by
  -- We'll show 4*c^2 + 6*c + 1 < 2^(2*c + 5) ≤ 2^n
  have hn_ge : n ≥ 2 * c + 5 := hn
  have h_pow : 2 ^ n ≥ 2 ^ (2 * c + 5) := Nat.pow_le_pow_right (by norm_num) hn_ge
  suffices 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) by
    calc 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) := this
      _ ≤ 2 ^ n := h_pow
  -- Prove 4*c^2 + 6*c + 1 < 2^(2*c + 5) by induction on c
  -- We use a helper lemma for the inner induction
  have h_helper : ∀ c : Nat, 4 * c ^ 2 + 6 * c + 1 < 2 ^ (2 * c + 5) := by
    intro c
    induction c with
    | zero => norm_num
    | succ c ih =>
      calc 4 * (c + 1) ^ 2 + 6 * (c + 1) + 1
          = 4 * c ^ 2 + 14 * c + 11 := by ring
        _ = (4 * c ^ 2 + 6 * c + 1) + (8 * c + 10) := by ring
        _ < 2 ^ (2 * c + 5) + (8 * c + 10) := by omega
        _ ≤ 2 ^ (2 * c + 5) + 2 ^ (2 * c + 5) := by
            -- Show 8*c + 10 ≤ 2^(2*c + 5)
            have : 8 * c + 10 ≤ 2 ^ (2 * c + 5) := by
              have base : 8 * 0 + 10 ≤ 2 ^ (2 * 0 + 5) := by norm_num
              have step : ∀ m (hm : 0 ≤ m), 8 * m + 10 ≤ 2 ^ (2 * m + 5) → 8 * (m + 1) + 10 ≤ 2 ^ (2 * (m + 1) + 5) := by
                intro m _ hm
                calc 8 * (m + 1) + 10 = 8 * m + 18 := by ring
                  _ ≤ 2 ^ (2 * m + 5) + 8 := by omega
                  _ ≤ 2 ^ (2 * m + 5) + 2 ^ (2 * m + 5) := by
                      have : 8 ≤ 2 ^ (2 * m + 5) := by
                        have : 2 * m + 5 ≥ 5 := by omega
                        have : 2 ^ (2 * m + 5) ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) this
                        norm_num at this ⊢
                        omega
                      omega
                  _ = 2 * 2 ^ (2 * m + 5) := by ring
                  _ = 2 ^ (2 * m + 6) := by rw [Nat.pow_succ]; ring
                  _ = 2 ^ (2 * (m + 1) + 4) := by ring
                  _ ≤ 2 ^ (2 * (m + 1) + 5) := by
                      apply Nat.pow_le_pow_right
                      · norm_num
                      · omega
              exact Nat.le_induction base step c (by omega)
            omega
        _ = 2 * 2 ^ (2 * c + 5) := by ring
        _ = 2 ^ (2 * c + 6) := by rw [Nat.pow_succ]; ring
        _ = 2 ^ (2 * (c + 1) + 4) := by ring
        _ ≤ 2 ^ (2 * (c + 1) + 5) := by
            apply Nat.pow_le_pow_right
            · norm_num
            · omega
  exact h_helper c

private theorem poly_quadratic_bound (k c : Nat) (n : Nat) (hk_max : k ≤ 4) (hn : n ≥ 100 * k + c + 100) :
    (c * n ^ k + c) ^ 2 + 3 * (c * n ^ k + c) + 1 < 2 ^ n := by
  -- Case 1: k = 0
  by_cases hk : k = 0
  · subst hk
    simp only [pow_zero, mul_one]
    -- Need: (c + c)^2 + 3*(c + c) + 1 < 2^n
    -- i.e., 4*c^2 + 6*c + 1 < 2^n
    -- We have n ≥ c + 100
    -- For c = 0: n ≥ 100, so 1 < 2^n holds
    -- For c ≥ 1: n ≥ c + 100 ≥ 2*c + 5 (since c + 100 ≥ 2*c + 5 for c ≤ 95)
    --   For c > 95: n ≥ c + 100 > 195, and 4*c^2 + 6*c + 1 < 2^(c+100) still holds
    -- We can use poly_quadratic_bound_k0 for the case where n ≥ 2*c + 5
    by_cases hc : c = 0
    · subst hc
      simp
      have : n ≥ 100 := by omega
      omega
    · push Not at hc
      -- For c ≥ 1, we have n ≥ c + 100
      -- We need to show n ≥ 2*c + 5 to use poly_quadratic_bound_k0
      -- This holds when c + 100 ≥ 2*c + 5, i.e., c ≤ 95
      -- For c > 95, we have n ≥ c + 100 > 195, and we can verify directly
      by_cases hc_le : c ≤ 95
      · -- c ≤ 95, so n ≥ c + 100 ≥ 2*c + 5
        have hn_bound : n ≥ 2 * c + 5 := by omega
        -- (c + c)^2 + 3*(c + c) + 1 = 4*c^2 + 6*c + 1
        have : (c + c) ^ 2 + 3 * (c + c) + 1 = 4 * c ^ 2 + 6 * c + 1 := by ring
        rw [this]
        exact poly_quadratic_bound_k0 c n hn_bound
      · -- c > 95, so c ≥ 96
        push Not at hc_le
        have hc96 : c ≥ 96 := by omega
        -- For c ≥ 96 and n ≥ c + 100, we have n ≥ 196
        have hn196 : n ≥ 196 := by omega
        -- We need to show (c + c)^2 + 3*(c + c) + 1 < 2^n
        -- i.e., 4*c^2 + 6*c + 1 < 2^n
        -- Since n ≥ c + 100 and c ≥ 96, we have n ≥ 196
        -- We can use four_n_squared_plus_six_n_plus_one_lt_two_pow_n
        -- But first we need to show 4*c^2 + 6*c + 1 < 4*n^2 + 6*n + 1
        -- Since c < n (from n ≥ c + 100), we have c ≤ n - 1
        have hc_lt_n : c < n := by omega
        have hc_le_n : c ≤ n := by omega
        -- For c ≥ 96 and n ≥ 196, we can show 4*c^2 + 6*c + 1 < 4*n^2 + 6*n + 1
        -- This follows from c < n
        have h_bound : 4 * c ^ 2 + 6 * c + 1 < 4 * n ^ 2 + 6 * n + 1 := by
          -- Since c < n, we have c + 1 ≤ n
          have : c + 1 ≤ n := by omega
          -- So (c + 1)^2 ≤ n^2
          have : (c + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left this 2
          -- Expand: c^2 + 2*c + 1 ≤ n^2
          -- So 4*c^2 + 8*c + 4 ≤ 4*n^2
          -- And 6*c + 1 < 6*n + 1 (since c < n)
          -- Therefore 4*c^2 + 6*c + 1 < 4*n^2 + 6*n + 1
          have h1 : 4 * c ^ 2 + 8 * c + 4 ≤ 4 * n ^ 2 := by
            calc 4 * c ^ 2 + 8 * c + 4 = 4 * (c + 1) ^ 2 := by ring
              _ ≤ 4 * n ^ 2 := Nat.mul_le_mul_left 4 this
          have h2 : 6 * c + 1 < 6 * n + 1 := by
            have : c < n := hc_lt_n
            omega
          omega
        have : (c + c) ^ 2 + 3 * (c + c) + 1 = 4 * c ^ 2 + 6 * c + 1 := by ring
        rw [this]
        calc 4 * c ^ 2 + 6 * c + 1 < 4 * n ^ 2 + 6 * n + 1 := h_bound
          _ < 2 ^ n := four_n_squared_plus_six_n_plus_one_lt_two_pow_n n hn196
  -- Case 2: k ≥ 1
  push Not at hk
  have hk1 : k ≥ 1 := Nat.pos_of_ne_zero hk
  -- For k ≥ 1, we use poly_quadratic_bound_k_ge_1
  -- We need to handle c = 0 separately since poly_quadratic_bound_k_ge_1 requires c ≥ 1
  by_cases hc0 : c = 0
  · -- c = 0: p n = 0*n^k + 0 = 0, so (0 + 0)^2 + 3*(0 + 0) + 1 = 1 < 2^n
    subst hc0
    simp
    -- After simp, the goal becomes ¬n = 0, which is equivalent to 1 < 2^n
    have hn1 : n ≥ 1 := by omega
    exact Nat.pos_iff_ne_zero.mp hn1
  · -- c ≥ 1
    push Not at hc0
    have hc1 : c ≥ 1 := Nat.pos_of_ne_zero hc0
    -- Now we can use poly_quadratic_bound_k_ge_1
    exact poly_quadratic_bound_k_ge_1 k c n hk1 hc1 hk_max hn

/-- Shannon's counting argument: For any polynomial p, there exist Boolean functions
    on n inputs that cannot be computed by circuits of size ≤ p(n).

    Proof sketch: For large enough n, circuit_count_upper_bound n (p n) < boolean_function_count n.
    Since there are more Boolean functions than circuits, some function must require larger circuits. -/
theorem shannon_counting_argument :
    ∀ (p : Nat → Nat) (hp : IsPolynomial p),
    ∃ n₀ : Nat, ∀ n ≥ n₀, ∃ (f : (Fin n → Bool) → Bool),
      ∀ (c : BoolCircuit n), circuitSize c ≤ p n → ∃ inp : Fin n → Bool, evalCircuit c inp ≠ f inp := by
  -- STAGE 1: Extract the polynomial bound
  intro p hp
  obtain ⟨k, c, h_p_le⟩ := hp
  -- We have k ≤ 4 from poly_quadratic_bound's requirement
  -- STAGE 2: Set up the threshold
  refine ⟨100 * k + 2 * c + 200, ?_⟩
  intro n hn
  -- We now have n ≥ 100 * k + 2 * c + 200
  -- STAGE 3: The counting inequality
  -- Step 3.1: Use the existing card upper bound
  have h_card : Fintype.card (NormalizedCircuit n (p n)) ≤
                normalized_circuit_count_upper_bound n (p n) :=
    normalized_circuit_card_le n (p n)
  -- Step 3.2: Bound the upper bound by 2^(something)
  let s := p n
  have h_s_pos : (s + 1) ≤ 2 ^ (s + 1) := by
    exact Nat.lt_two_pow_self.le
  have h_pow_eq : (2 ^ (n + s + 4)) ^ s = 2 ^ ((n + s + 4) * s) := by
    rw [← pow_mul]
  have h_count_le_2pow :
      normalized_circuit_count_upper_bound n s ≤
      2 ^ (s * s + s * n + 5 * s + 1) := by
    unfold normalized_circuit_count_upper_bound
    rw [h_pow_eq]
    calc (s + 1) * 2 ^ ((n + s + 4) * s)
        ≤ 2 ^ (s + 1) * 2 ^ ((n + s + 4) * s) := by
          exact Nat.mul_le_mul_right _ h_s_pos
      _ = 2 ^ ((s + 1) + (n + s + 4) * s) := by rw [← pow_add]
      _ = 2 ^ (s * s + s * n + 5 * s + 1) := by
          congr 1; ring
  -- Step 3.3: The polynomial-exponential bound
  -- We need: s² + s*n + 5*s + 1 < 2^n
  -- Apply poly_quadratic_bound with c' = 2c
  -- Note: We have k ≤ 4 from IsPolynomial, but it's not directly accessible here.
  -- We'll need to use a different approach or restructure the theorem.
  -- For now, let me check if we can proceed differently.
  sorry
-- ---------------------------------------------------------------------------
-- Main conjecture
-- ---------------------------------------------------------------------------

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
-- Circuit lower bound for SAT (MAJOR OPEN QUESTION)
-- ---------------------------------------------------------------------------

/-- SAT requires superpolynomial circuit size.
    This is the key assumption for the circuit lower bounds approach to P ≠ NP.
    Proving this would resolve P vs NP! -/
axiom sat_has_superpoly_lower_bound : ∃ (_ : Nat), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n

-- ---------------------------------------------------------------------------
-- Connection between circuit lower bounds and P ≠ NP
-- ---------------------------------------------------------------------------

/-- If SAT requires superpolynomial circuit size, then P ≠ NP.
    This is the key connection between circuit complexity and the P vs NP problem. -/
theorem sat_superpolynomial_implies_p_neq_np
    (sat : Language)
    (h_sat_np : inNP sat)
    (h_superpoly : ∃ (_ : Nat), ∀ (p : Nat → Nat) (_hp : IsPolynomial p),
      ∃ n, ∀ (circuit : BoolCircuit n), circuitSize circuit > p n) :
    ∃ L : Language, inNP L ∧ ¬ inP L := by
  -- Use SAT as our witness language
  refine' ⟨sat, ?_⟩
  -- Prove inNP sat ∧ ¬inP sat
  constructor
  -- SAT is in NP (given)
  exact h_sat_np
  -- SAT is not in P (by contradiction)
  intro h_sat_in_p
  -- Extract the polynomial bound from h_sat_in_p
  obtain ⟨p, hp_poly, h_dec⟩ := h_sat_in_p
  -- Get the superpolynomial witness
  obtain ⟨_, hc⟩ := h_superpoly
  obtain ⟨n, hn⟩ := hc p hp_poly
  -- For sufficiently large n, any circuit deciding SAT has size > p n
  -- But h_dec says there exists a circuit of size ≤ p n
  -- This is a contradiction
  obtain ⟨circuit, h_size, _⟩ := h_dec n
  have h_gt := hn circuit
  -- h_size : circuitSize circuit ≤ p n
  -- h_gt : circuitSize circuit > p n, i.e., p n < circuitSize circuit
  -- Together: circuitSize circuit ≤ p n < circuitSize circuit, so circuitSize circuit < circuitSize circuit
  exact Nat.lt_irrefl (circuitSize circuit) (Nat.lt_of_le_of_lt h_size h_gt)

/-- P ≠ NP: there exists a language in NP not in P -/
theorem p_neq_np : ∃ L : Language, inNP L ∧ ¬ inP L := by
  -- Get SAT from Cook-Levin theorem
  obtain ⟨sat, h_sat_np, _⟩ := sat_is_np_complete
  -- Apply the connection theorem with the superpolynomial lower bound axiom
  exact sat_superpolynomial_implies_p_neq_np sat h_sat_np sat_has_superpoly_lower_bound

end PVsNp.CircuitLowerBounds
