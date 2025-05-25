/-
SECTION 1: PRIMITIVE IDEAS AND PROPOSITIONS

From pages 0136-0141 of Principia Mathematica

"The purpose of the present section is to set forth the first stage of the
deduction of pure mathematics from its logical foundations. This first stage is
necessarily concerned with deduction itself, i.e., with the principles by which
conclusions are inferred from premises."

This section establishes the fundamental logical propositions that serve as the
foundation for all subsequent mathematical reasoning.
-/

import Mathlib.Logic.Basic

namespace Principia.Part1.Section1

-- PRIMITIVE IDEAS

/-
From page 0139: "∗1·01. p ⊃ q . =. ∼ p ∨ q Df."
"Here the letters 'Df' stand for 'definition.' They and the sign of equality
together are to be regarded as forming one symbol, standing for 'is defined
to mean.'"
-/
theorem th_1_01 (p q: Prop) : (p → q) = (¬p ∨ q) := by
  apply propext
  exact imp_iff_not_or

-- PRIMITIVE PROPOSITIONS

/-
From page 0140: "∗1·1. Anything implied by a true elementary proposition is true. Pp†."
This is the fundamental principle of modus ponens.
-/
theorem th_1_1 (p q: Prop) : (p → q) → (p → q) := by
  intro h
  exact h

/-
From page 0141: "∗1·2. ⊢ : p ∨ p . ⊃ . p Pp."
"This proposition states: 'If either p is true or p is true, then p is true.'
It is called the 'principle of tautology,' and will be quoted by the abbreviated
title of 'Taut.'"
-/
theorem th_1_2 (p: Prop) : (p ∨ p) → p := by
  intro h
  cases h with
  | inl hp => exact hp
  | inr hp => exact hp

/-
From page 0141: "∗1·3. ⊢ : q . ⊃ . p ∨ q Pp."
"This principle states: 'If q is true, then 'p or q' is true.' Thus e.g. if q is
'to-day is Wednesday' and p is 'to-day is Tuesday,' the principle states:
'If to-day is Wednesday, then to-day is either Tuesday or Wednesday.' It is called
the 'principle of addition,' because it states that if a proposition is true, any
alternative may be added without making it false. The principle will be referred
to as 'Add.'"
-/
theorem th_1_3 (p q: Prop) : q → (p ∨ q) := by
  intro hq
  exact Or.inr hq

/-
From page 0141: "∗1·4. ⊢ : p ∨ q . ⊃ . q ∨ p Pp."
"This principle states that 'p or q' implies 'q or p.' It states the permutative
law for logical addition of propositions, and will be called the 'principle of
permutation.' It will be referred to as 'Perm.'"
-/
theorem th_1_4 (p q: Prop) : (p ∨ q) → (q ∨ p) := by
  intro h
  exact Or.symm h

/-
From page 0141: "∗1·5. ⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r) Pp."
"This principle states: 'If either p is true, or 'q or r' is true, then either
q is true, or 'p or r' is true.' It is a form of the associative law for logical
addition, and will be called the 'associative principle.' It will be referred to
as 'Assoc.'"
-/
theorem th_1_5 (p q r: Prop) : p ∨ (q ∨ r) → q ∨ (p ∨ r) := by
  intro h
  cases h with
  | inl hp => exact Or.inr (Or.inl hp)
  | inr hqr => 
    cases hqr with
    | inl hq => exact Or.inl hq
    | inr hr => exact Or.inr (Or.inr hr)

/-
From page 0142: "∗1·6. ⊢ : . q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r Pp."
"This principle states: 'If q implies r, then 'p or q' implies 'p or r.'' In
other words, in an implication, an alternative may be added to both premiss
and conclusion without impairing the truth of the implication. The principle
will be called the 'principle of summation,' and will be referred to as 'Sum.'"
-/
theorem th_1_6 (p q r: Prop) : (q → r) → ((p ∨ q) → (p ∨ r)) := by
  intro hqr hpq
  cases hpq with
  | inl hp => exact Or.inl hp
  | inr hq => exact Or.inr (hqr hq)

/-
From page 0142: "∗1·7. If p is an elementary proposition, ∼ p is an elementary proposition. Pp."
This establishes that negation preserves the elementary nature of propositions.
-/
-- This is more of a meta-principle about what constitutes elementary propositions
-- In Lean, we don't need to prove this as it's built into the type system

/-
From page 0142: "∗1·71. If p and q are elementary propositions, p ∨ q is an elementary proposition. Pp."
This establishes that disjunction of elementary propositions is elementary.
-/
-- Similarly, this is built into Lean's type system

/-
From page 0142: "∗1·72. If φp and ψp are elementary propositional functions which take
elementary propositions as arguments, φp ∨ ψp is an elementary propositional function. Pp."
This extends the principle to propositional functions.
-/
-- This is also meta-theoretical and built into Lean's type system

end Principia.Part1.Section1