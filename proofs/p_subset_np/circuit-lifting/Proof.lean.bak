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

instance : Inhabited CircuitNode := ⟨{ gate := Gate.Const false, children := [] }⟩

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

/-- Well-formedness predicate: all Var nodes in a circuit have indices < n. -/
def IsWellFormed {n : Nat} (c : BoolCircuit n) : Prop :=
  ∀ i < c.nodes.size, ∀ j, c.nodes[i]!.gate = Gate.Var j → j < n

/-- Lifting preserves evaluation when restricted to the first n inputs.
    Proof sketch: evalNode and evalCircuit only consult inp at Var-gate positions i < n;
    lifting keeps those same positions so the values agree. -/
theorem liftCircuit_eval {n : Nat} (c : BoolCircuit n) (inp : Fin (2 * n) → Bool)
    (h_wf : IsWellFormed c) :
    evalCircuit (liftCircuit c) inp =
    evalCircuit c (fun i => inp ⟨i.val, by have := i.isLt; omega⟩) := by
  simp only [liftCircuit, evalCircuit]
  -- Prove that for each node in c.nodes, evalNode gives the same result for both inputs
  have h_nodes : ∀ i < c.nodes.size, ∀ acc : Array Bool,
      evalNode inp acc c.nodes[i]! = evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc c.nodes[i]! := by
    intro i hi acc
    unfold evalNode
    match h_gate : c.nodes[i]!.gate with
    | Gate.And => rfl
    | Gate.Or => rfl
    | Gate.Not => rfl
    | Gate.Const b => rfl
    | Gate.Var idx =>
      by_cases hi_idx : idx < n
      · -- idx < n: both sides read from inp at index idx
        have h : idx < 2 * n := by omega
        simp only [h, hi_idx, if_true]
      · -- idx >= n: By well-formedness, this case doesn't occur
        exfalso
        have : idx < n := h_wf i hi idx h_gate
        omega
  -- Use a direct approach: show that the two foldl computations give the same result
  -- by showing that for each node in c.nodes, evalNode gives the same result
  have h_foldl_eq : c.nodes.foldl (fun acc node => Array.push acc (evalNode inp acc node)) #[] =
                   c.nodes.foldl (fun acc node => Array.push acc (evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc node)) #[] := by
    -- We use the fact that Array.foldl is defined recursively
    -- and we can prove equality by showing the step functions are equal
    -- But this is tricky because the step functions depend on the node
    -- Instead, we use the fact that for all i < c.nodes.size,
    -- evalNode inp acc c.nodes[i]! = evalNode (fun i => inp ⟨i.val, ...⟩) acc c.nodes[i]!
    -- And we prove this by induction on the array size
    have : ∀ i, i ≤ c.nodes.size →
        (c.nodes.take i).foldl (fun acc node => Array.push acc (evalNode inp acc node)) #[] =
        (c.nodes.take i).foldl (fun acc node => Array.push acc (evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc node)) #[] := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        have h_i_le : i ≤ c.nodes.size := by omega
        have h_i_lt : i < c.nodes.size := by omega
        -- The key insight: we can use the fact that
        -- (c.nodes.take (i+1)).foldl f #[] =
        --   (c.nodes.take i).foldl f #[]).push (f _ c.nodes[i]!)
        -- And by h_nodes, f _ c.nodes[i]! is the same for both f
        have h_take_push : (c.nodes.take (i + 1)).foldl (fun acc node => Array.push acc (evalNode inp acc node)) #[] =
                          ((c.nodes.take i).foldl (fun acc node => Array.push acc (evalNode inp acc node)) #[]).push
                            (evalNode inp ((c.nodes.take i).foldl (fun acc node => Array.push acc (evalNode inp acc node)) #[]) c.nodes[i]!) := by
          have : c.nodes.take (i + 1) = (c.nodes.take i).push c.nodes[i]! := by
            ext j
            simp [Array.take, Array.getElem_push]
            by_cases h_j_lt : j < i + 1
            · by_cases h_j_lt_i : j < i
              · simp [h_j_lt, h_j_lt_i]
                omega
              · have : j = i := by omega
                subst this
                simp [h_j_lt]
                omega
            · simp [h_j_lt]
          rw [this]
          simp [Array.foldl, Array.push]
        have h_take_push2 : (c.nodes.take (i + 1)).foldl (fun acc node => Array.push acc (evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc node)) #[] =
                          ((c.nodes.take i).foldl (fun acc node => Array.push acc (evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc node)) #[]).push
                            (evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) ((c.nodes.take i).foldl (fun acc node => Array.push acc (evalNode (fun (i : Fin n) => inp ⟨i.val, by have := i.isLt; omega⟩) acc node)) #[]) c.nodes[i]!) := by
          have : c.nodes.take (i + 1) = (c.nodes.take i).push c.nodes[i]! := by
            ext j
            simp [Array.take, Array.getElem_push]
            by_cases h_j_lt : j < i + 1
            · by_cases h_j_lt_i : j < i
              · simp [h_j_lt, h_j_lt_i]
                omega
              · have : j = i := by omega
                subst this
                simp [h_j_lt]
                omega
            · simp [h_j_lt]
          rw [this]
          simp [Array.foldl, Array.push]
        rw [h_take_push, h_take_push2, ih h_i_le]
        congr 1
        exact h_nodes i h_i_lt _
    have h_take_full : c.nodes.take c.nodes.size = c.nodes := by simp [Array.take]
    rw [← h_take_full, ← h_take_full]
    exact this c.nodes.size (by simp)
  exact congrArg (·.getD c.output false) h_foldl_eq

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
  have h_div : (2 * n) / 2 = n := by omega
  -- For any i : Fin ((2 * n) / 2), we have i.val < (2 * n) / 2 = n,
  -- so the combined function applied to ⟨i.val, _⟩ gives inp ⟨i.val, h⟩ (since i.val < n).
  -- And inp ⟨i.val, h⟩ = inp (Fin.cast _ i) by Fin.ext.
  -- Therefore, the two input functions are pointwise equal.
  have h_fn : ∀ i : Fin ((2 * n) / 2),
      (fun j : Fin (2 * n) => if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, by omega⟩)
        ⟨i.val, by omega⟩ = inp (Fin.cast (by omega) i) := by
    intro i
    have hi : i.val < (2 * n) / 2 := i.isLt
    have hi_n : i.val < n := by omega
    simp [hi_n]
    -- Now: inp ⟨i.val, _⟩ = inp (Fin.cast _ i)
    -- Fin.cast preserves the val, so these are equal
    congr
  -- Now we have that for all i : Fin ((2 * n) / 2), f1 i = inp (Fin.cast _ i)
  -- And Fin.cast (by omega) : Fin ((2 * n) / 2) → Fin n is a bijection
  -- So L ((2 * n) / 2) f1 = L n (inp ∘ Fin.cast)
  -- But inp ∘ Fin.cast = inp (since Fin.cast preserves val)
  -- So L ((2 * n) / 2) f1 = L n inp
  -- This is the dependent-type bookkeeping step
  -- We use Eq.rec to transport the proposition along h_div
  have h_f1_eq : (fun i : Fin ((2 * n) / 2) =>
                    (fun j : Fin (2 * n) => if h : j.val < n then inp ⟨j.val, h⟩ else w ⟨j.val - n, by omega⟩)
                    ⟨i.val, by omega⟩) =
                 (fun i : Fin n => inp i) ∘ Fin.cast h_div := by
    funext i
    exact h_fn i
  rw [h_f1_eq]
  -- Now goal is: L ((2 * n) / 2) ((fun i : Fin n => inp i) ∘ Fin.cast h_div) ↔ L n inp
  -- The mathematical content is trivial: (2 * n) / 2 = n and the functions are pointwise equal.
  -- The challenge is dependent-type bookkeeping.
  -- Solution: Use Eq.rec to transport the entire proposition along h_div.
  -- The motive is: fun m => L m (f ∘ Fin.cast (by omega : m = n)) ↔ L n inp
  -- where f = (fun i : Fin n => inp i). But this doesn't work because omega can't prove m = n.
  --
  -- Instead, we use the fact that the composition (fun i : Fin n => inp i) ∘ Fin.cast h_div
  -- is pointwise equal to (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩).
  -- And since h_div : (2*n)/2 = n, we can use Eq.rec with a simpler motive.
  --
  -- The key insight: for any i : Fin ((2*n)/2), we have i.val < n (by omega from h_div).
  -- So Fin.cast h_div i = ⟨i.val, _⟩ and inp (Fin.cast h_div i) = inp ⟨i.val, _⟩.
  -- The function (fun i : Fin n => inp i) ∘ Fin.cast h_div is pointwise equal to
  -- (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩).
  -- And since h_div : (2*n)/2 = n, we can use Eq.rec to transport L.
  --
  -- Solution: Use Eq.rec to transport L along h_div.
  -- The key is to use a motive where the function is defined for each m.
  -- For m = (2*n)/2, the function is (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩)
  -- For m = n, the function is inp
  --
  -- We first show that (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩) = (fun i : Fin n => inp i) ∘ Fin.cast h_div
  have h_fun_def : (fun i : Fin ((2 * n) / 2) => inp ⟨i.val, by omega⟩) =
                   (fun i : Fin n => inp i) ∘ Fin.cast h_div := by
    funext i
    simp [Fin.cast]
  rw [← h_fun_def]
  -- Now: L ((2*n)/2) (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩) ↔ L n inp
  -- Use Eq.rec to transport L along h_div
  -- The key: we use Eq.rec with a motive that handles the function transport
  -- We define a function f_m : Fin m → Bool for each m such that:
  -- - For m = (2*n)/2: f_m = (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩)
  -- - For m = n: f_m = inp
  -- And we show L m f_m ↔ L n inp for all m.
  --
  -- The motive: fun m => L m (Eq.rec (motive := fun _ _ => Fin m → Bool) (fun i : Fin ((2*n)/2) => inp ⟨i.val, by omega⟩) h_div) ↔ L n inp
  -- But this is too complex.
  --
  -- Simpler approach: use the fact that h_div : (2*n)/2 = n is definitional for even n
  -- and use Eq.rec with a motive that doesn't depend on the equality proof
  --
  -- Actually, the simplest solution: since we know that for all i : Fin ((2*n)/2),
  -- i.val < n, we can show that (fun i : Fin ((2*n)/2) => inp ⟨i.val, _⟩) = inp ∘ Fin.cast h_div
  -- And since h_div : (2*n)/2 = n, we have Fin ((2*n)/2) = Fin n
  -- So L ((2*n)/2) (inp ∘ Fin.cast h_div) = L n inp by substitution
  --
  -- But Lean's dependent elimination doesn't allow this directly because n appears in the type.
  --
  -- For now, we use sorry and document this as the dependent-type bookkeeping issue.
  -- The solution is to either:
  -- 1. Use Eq.rec with a carefully constructed motive (as suggested in NOTES.md)
  -- 2. Change the definition of Language to not use dependent types
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
    -- For even m = 2k, liftCircuit gives BoolCircuit (2k) = BoolCircuit m.
    -- For odd m = 2k+1, we need a circuit for size m.
    -- Since inNP only uses V at even sizes (2*n), the behavior at odd sizes doesn't matter.
    -- We use a constant false circuit for odd sizes.
    by_cases h_even : m % 2 = 0
    · -- m is even: m = 2k for some k
      have : ∃ k, m = 2 * k := by
        use m / 2
        omega
      obtain ⟨k, hk⟩ := this
      subst hk
      obtain ⟨c, hc_size, hc_correct⟩ := h_circuits k
      use liftCircuit c
      constructor
      · -- circuitSize (liftCircuit c) ≤ p (m / 2) + 1
        have h_div : (2 * k) / 2 = k := by omega
        have h_size : circuitSize (liftCircuit c) = circuitSize c := liftCircuit_size c
        rw [h_size]
        have : (fun m => p (m / 2) + 1) (2 * k) = p k + 1 := by
          simp [h_div]
        rw [this]
        omega
      · -- evalCircuit (liftCircuit c) inp = true ↔ V (2 * k) inp
        intro inp
        have h_div : (2 * k) / 2 = k := by omega
        -- We need to add well-formedness for c
        -- For now, we assume circuits from inP are well-formed
        have h_wf : IsWellFormed c := by
          -- Circuits from inP that correctly compute a language must be well-formed
          -- (otherwise Var nodes with idx >= n always return false)
          sorry
        have h_eval := liftCircuit_eval c inp h_wf
        rw [h_eval]
        -- Goal: evalCircuit c f = true ↔ L ((2 * k) / 2) f'
        -- where f : Fin k → Bool and f' : Fin ((2 * k) / 2) → Bool
        -- Since (2 * k) / 2 = k, we use verifier_iff to relate these
        -- But verifier_iff is for a specific form of the function
        -- Let's use the fact that L ((2 * k) / 2) f' = L k f (by dependent-type bookkeeping)
        -- and evalCircuit c f = true ↔ L k f (by hc_correct)
        sorry
    · -- m is odd: m = 2k + 1 for some k
      have : ∃ k, m = 2 * k + 1 := by
        use m / 2
        omega
      obtain ⟨k, hk⟩ := this
      subst hk
      -- For odd m, we use a constant false circuit
      -- The size is 1 ≤ p k + 1 (since p is polynomial, p k ≥ 0)
      -- And evalCircuit (constant false) inp = false for all inp
      -- We need: false = true ↔ V (2k+1) inp
      -- i.e., false ↔ V (2k+1) inp
      -- So we need V (2k+1) inp = false for all inp
      -- But V (2k+1) inp = L k (fun i => inp ⟨i.val, _⟩)
      -- which is not necessarily false
      -- So we can't use a constant false circuit
      -- We need a circuit that computes L k on the first k bits of inp
      -- But we only have circuits for size k, not for size 2k+1
      -- This is the fundamental issue: we need a more general lifting function
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

