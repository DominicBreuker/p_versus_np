-- Time Hierarchy Theorem — Lean4 formalization stub
-- Goal: Prove DTIME(f(n)) ⊊ DTIME(g(n)) for appropriate f, g.
-- Status: Initial stub — core definitions present; proofs use `sorry` as placeholders.

namespace PVsNp.TimeHierarchy

-- ---------------------------------------------------------------------------
-- Languages and deciders
-- ---------------------------------------------------------------------------

/-- A language on binary words -/
abbrev Lang := List Bool → Prop

/-- An abstract decider: maps a word to a Boolean answer -/
abbrev Decider := List Bool → Bool

/-- M decides language L -/
def decides (M : Decider) (L : Lang) : Prop :=
  ∀ w, M w = true ↔ L w

-- ---------------------------------------------------------------------------
-- Abstract step-count model
-- ---------------------------------------------------------------------------

/-- The number of steps M takes on input w (axiomatized for now) -/
noncomputable def timeOf (M : Decider) (w : List Bool) : Nat := sorry

-- ---------------------------------------------------------------------------
-- DTIME complexity class (as a predicate on languages)
-- ---------------------------------------------------------------------------

/-- L ∈ DTIME(f): L is decidable within f(|w|) steps -/
def inDTIME (f : Nat → Nat) (L : Lang) : Prop :=
  ∃ M : Decider, decides M L ∧ ∀ w, timeOf M w ≤ f w.length

-- ---------------------------------------------------------------------------
-- Basic lemmas
-- ---------------------------------------------------------------------------

/-- DTIME is monotone: a tighter bound gives a subset class -/
theorem inDTIME_mono {f g : Nat → Nat} (h : ∀ n, f n ≤ g n) (L : Lang)
    (hL : inDTIME f L) : inDTIME g L := by
  obtain ⟨M, hd, ht⟩ := hL
  exact ⟨M, hd, fun w => Nat.le_trans (ht w) (h w.length)⟩

/-- If two bounds agree, the DTIME classes are equal -/
theorem inDTIME_congr {f g : Nat → Nat} (h : ∀ n, f n = g n) (L : Lang) :
    inDTIME f L ↔ inDTIME g L :=
  ⟨inDTIME_mono (fun n => h n ▸ Nat.le_refl _) L,
   inDTIME_mono (fun n => (h n).symm ▸ Nat.le_refl _) L⟩

-- ---------------------------------------------------------------------------
-- Strict inclusion (DTIME(f) ⊊ DTIME(g))
-- ---------------------------------------------------------------------------

/-- DTIME(f) is a strict subset of DTIME(g) -/
def DTIME_strictSubset (f g : Nat → Nat) : Prop :=
  (∀ L, inDTIME f L → inDTIME g L) ∧  -- subset direction
  ∃ L, inDTIME g L ∧ ¬ inDTIME f L    -- there exists L in DTIME(g) \ DTIME(f)

-- ---------------------------------------------------------------------------
-- Time-constructibility
-- ---------------------------------------------------------------------------

/-- f is time-constructible if a decider can compute the unary representation of f(n)
    in O(f(n)) steps -/
def IsTimeConstructible (f : Nat → Nat) : Prop :=
  ∃ M : Decider, ∀ n, timeOf M (List.replicate n false) ≤ f n

-- ---------------------------------------------------------------------------
-- Universal simulation (key axiom)
-- ---------------------------------------------------------------------------

/-- Pairing: encode a natural number index i with a word w.
    Represents (i, w) as i false-bits, a true separator, then w.
    Length: encode i w has length i + 1 + w.length.
    Injective: encode i v = encode j w → i = j ∧ v = w (by counting leading false-bits). -/
def encode (i : Nat) (w : List Bool) : List Bool :=
  List.replicate i false ++ [true] ++ w

/-- The universal simulator -/
noncomputable def universal : Decider := sorry

/-- Universal simulation axiom: universal simulates any decider M_i within a
    quadratic step overhead (classical proof gives log-factor; quadratic simplifies axiom) -/
axiom universal_simulation (M : Decider) (f : Nat → Nat)
    (hM : ∀ w, timeOf M w ≤ f w.length) :
    ∃ i : Nat, ∀ v,
      universal (encode i v) = M v ∧
      timeOf universal (encode i v) ≤ f v.length * (f v.length + 1)

-- ---------------------------------------------------------------------------
-- Main theorem (stated; proof deferred)
-- ---------------------------------------------------------------------------

/-- Time Hierarchy Theorem (informal statement):
    If f(n) * (f(n) + 1) = o(g(n)) and f is time-constructible,
    then DTIME(f) ⊊ DTIME(g). -/
theorem time_hierarchy_theorem (f g : Nat → Nat)
    (_hf_tc : IsTimeConstructible f)
    (_hfg : ∀ n, f n * (f n + 1) < g n) :
    DTIME_strictSubset f g := by
  constructor
  · -- Monotonicity: DTIME(f) ⊆ DTIME(g)
    intro L hL
    exact inDTIME_mono (fun n => Nat.le_of_lt (Nat.lt_of_le_of_lt
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (_hfg n))) L hL
  · -- Diagonalization: ∃ L ∈ DTIME(g) \ DTIME(f)
    sorry

end PVsNp.TimeHierarchy

