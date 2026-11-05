import Mathlib.Tactic.NormNum

namespace G0002

def Sat {α β : Type} (C : β → α → Prop) (w : α → Prop) : Prop :=
  ∀ b, ∃ a, C b a ∧ w a

def erase {α : Type} (w : α → Prop) (i : α) : α → Prop :=
  fun a => w a ∧ a ≠ i

def First {α β : Type} (C : β → α → Prop) (w : α → Prop) (i : α) : Prop :=
  w i ∧ ¬ Sat C (erase w i)

def Second {α β : Type} (C : β → α → Prop) (w : α → Prop) (i : α) : Prop :=
  First C w i ∨ ∃ j, w j ∧ i ≠ j ∧ Sat C (erase w j) ∧
    ¬ Sat C (erase (erase w j) i)

-- A two-positive clause whose endpoints are not first pivots supplies
-- a genuine second-order, non-first coordinate pivot.
theorem pair_witness {α β : Type} (C : β → α → Prop) (w : α → Prop)
    (i j : α) (b : β) (_wi : w i) (wj : w j) (hij : i ≠ j)
    (si : Sat C (erase w i)) (sj : Sat C (erase w j))
    (pair : ∀ a, C b a → w a → a = i ∨ a = j) :
    Second C w i ∧ ¬ First C w i := by
  have killed : ¬ Sat C (erase (erase w j) i) := by
    intro hs
    obtain ⟨a, ha, hw⟩ := hs b
    rcases pair a ha hw.1.1 with hi | hj
    · exact hw.2 hi
    · exact hw.1.2 hj
  constructor
  · exact Or.inr ⟨j, wj, hij, sj, killed⟩
  · intro h
    exact h.2 si

-- Exact rational margins used in the finite probabilistic certificate.
example : (1000000 : ℚ)^2 / 12 -
    288 * (1000000 : ℚ)^3 / 100000000000000 ≥
    (1000000 : ℚ)^2 / 24 := by norm_num

example : (1000000 : ℚ)^2 / 2592 > 10 * 10000000 := by norm_num

example : 5 * ((100000000000000 : ℚ) + 4) ≤
    6 * 100000000000000 := by norm_num

example : (32 : ℚ) / 3 * (1000000 : ℚ)^2 / 100000000000000 < 1 := by
  norm_num

example : (1000000 : ℚ) * (2 / 10000000 + 2 / 100000000000000) < 1 / 4 := by
  norm_num

end G0002
