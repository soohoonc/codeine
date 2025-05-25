/-
SECTION 3: THE LOGICAL PRODUCT OF TWO PROPOSITIONS

From pages 0154-0155 of Principia Mathematica

"The logical product of two propositions p and q is practically the proposition
'p and q are both true.' But this as it stands would have to be a new primitive
idea. We therefore take as the logical product the proposition ∼(∼p ∨ ∼q), 
i.e. 'it is false that either p is false or q is false,' which is obviously true 
when and only when p and q are both true."

This section introduces conjunction (logical product) and derives its basic properties.
-/

import Mathlib.Logic.Basic
import Principia.Section1
import Principia.Section2

namespace Principia.Part1.Section3

open Principia.Part1.Section1 Principia.Part1.Section2

/-
From page 0154: "∗3·01. p . q . = . ∼ (∼ p ∨ ∼ q) Df"
"where 'p . q' is the logical product of p and q."

This defines conjunction in terms of negation and disjunction.
-/
def logical_product (p q : Prop) : Prop := ¬(¬p ∨ ¬q)

-- We use Lean's built-in conjunction, but prove equivalence
theorem th_3_01 (p q : Prop) : (p ∧ q) = ¬(¬p ∨ ¬q) := by
  apply propext
  constructor
  · intro ⟨hp, hq⟩
    intro h
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq
  · intro h
    constructor
    · by_contra hnp
      exact h (Or.inl hnp)
    · by_contra hnq
      exact h (Or.inr hnq)

/-
From page 0154: "∗3·02. p ⊃ q ⊃ r . = . p ⊃ q . q ⊃ r Df"
"This definition serves merely to abbreviate proofs."

This introduces a notation for nested implications.
-/
theorem th_3_02 (p q r : Prop) : (p → (q → r)) = ((p → q) ∧ (q → r)) := by
  apply propext
  constructor
  · intro h
    constructor
    · intro hp
      intro hq
      exact h hp hq
    · intro hq
      intro hp
      exact h hp hq
  · intro ⟨hpq, hqr⟩ hp hq
    exact hqr hq

/-
From page 0155: "∗3·2. ⊢ : . p . ⊃ : q . ⊃ . p . q"
"I.e. 'p implies that q implies p . q,' i.e. if each of two propositions is true,
so is their logical product."
-/
theorem th_3_2 (p q : Prop) : p → (q → (p ∧ q)) := by
  intro hp hq
  exact ⟨hp, hq⟩

/-
From page 0155: "∗3·26. ⊢ : p . q . ⊃ . p"
∗3·27. ⊢ : p . q . ⊃ . q

"I.e. if the logical product of two propositions is true, then each of the two
propositions severally is true."
-/
theorem th_3_26 (p q : Prop) : (p ∧ q) → p := by
  intro ⟨hp, _⟩
  exact hp

theorem th_3_27 (p q : Prop) : (p ∧ q) → q := by
  intro ⟨_, hq⟩
  exact hq

/-
From page 0155: "∗3·3. ⊢ : . p . q . ⊃ . r : ⊃ : p . ⊃ . q ⊃ r"
"I.e. if p and q jointly imply r, then p implies that q implies r. This
principle (following Peano) will be called 'exportation,' because q is 'exported'
from the hypothesis. It will be referred to as 'Exp.'"
-/
theorem th_3_3 (p q r : Prop) : ((p ∧ q) → r) → (p → (q → r)) := by
  intro h hp hq
  exact h ⟨hp, hq⟩

/-
From page 0155: "∗3·31. ⊢ : . p . ⊃ . q ⊃ r : ⊃ : p . q . ⊃ . r"
"This is the correlative of the above, and will be called (following Peano)
'importation' (referred to as 'Imp')."
-/
theorem th_3_31 (p q r : Prop) : (p → (q → r)) → ((p ∧ q) → r) := by
  intro h ⟨hp, hq⟩
  exact h hp hq

/-
From page 0155: "∗3·35. ⊢ : p . p ⊃ q . ⊃ . q"
"I.e. 'if p is true, and q follows from it, then q is true.' This will be called
the 'principle of assertion' (referred to as 'Ass'). It differs from ∗1·1 by
the fact that it does not apply only when p really is true, but requires merely
the hypothesis that p is true."
-/
theorem th_3_35 (p q : Prop) : (p ∧ (p → q)) → q := by
  intro ⟨hp, hpq⟩
  exact hpq hp

/-
From page 0155: "∗3·43. ⊢ : . p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q . r"
"I.e. if a proposition implies each of two propositions, then it implies their
logical product. This is called by Peano the 'principle of composition.' It
will be referred to as 'Comp.'"
-/
theorem th_3_43 (p q r : Prop) : ((p → q) ∧ (p → r)) → (p → (q ∧ r)) := by
  intro ⟨hpq, hpr⟩ hp
  exact ⟨hpq hp, hpr hp⟩

/-
From page 0155: "∗3·45. ⊢ : . p ⊃ q . ⊃ : p . r . ⊃ . q . r"
"I.e. both sides of an implication may be multiplied by a common factor.
This is called by Peano the 'principle of the factor.' It will be referred to
as 'Fact.'"
-/
theorem th_3_45 (p q r : Prop) : (p → q) → ((p ∧ r) → (q ∧ r)) := by
  intro hpq ⟨hp, hr⟩
  exact ⟨hpq hp, hr⟩

end Principia.Part1.Section3