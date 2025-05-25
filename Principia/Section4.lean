/-
Section 4: Equivalence and Formal Rules

From page 0160.png - "*4. EQUIVALENCE AND FORMAL RULES"

Summary of *4:
"In this number, we shall be concerned with rules analogous, more or less, 
to those of ordinary algebra. It is from these rules that the usual 'calculus' 
of formal logic starts. Treated as a 'calculus,' the rules of deduction are 
capable of many other interpretations. But all other interpretations depend 
upon the one here considered, since in all of them we deduce consequences 
from our rules, and thus presuppose the theory of deduction."

The fundamental principle is that numbers which are all either 0 or 1; 
"p ⊃ q" is to have the value 0 if p is 1 and q is 0; otherwise it is to have 
the value 1; "~p" is to be 1 if p is 0, and to be 0 if p is 1; "p ∨ q" is to 
be 1 if p and q are both 0, and is to be 1 in any other case; and the 
assertion-sign is to mean that what follows has the value 1.
-/

import Mathlib.Logic.Basic
import Principia.Section1
import Principia.Section2
import Principia.Section3

namespace Principia.Part1.Section4

open Principia.Part1.Section1 Principia.Part1.Section2 Principia.Part1.Section3

-- *4.01 Equivalence Definition
--- When each of two propositions implies the other, we say that the two are 
--- equivalent, which we write "p ≡ q." We put
--- *4.01: p ≡ q . = . p ⊃ q . q ⊃ p Df
--- It is obvious that two propositions are equivalent when, and only when, 
--- both are true or both are false. Following Frege, we shall call the truth-
--- value of a proposition truth if it is true, and falsehood if it is false. 
--- Thus two propositions are equivalent when they have the same truth-value.

def equivalent (p q : Prop) : Prop := (p → q) ∧ (q → p)

notation p " ≡ " q => equivalent p q

theorem th_4_01 (p q : Prop) : (p ≡ q) = ((p → q) ∧ (q → p)) := by
  rfl

-- Truth-function definition
--- It should be observed that, if p ≡ q, q may be substituted for p without 
--- altering the truth-value of any function of p which involves no primitive 
--- ideas except those enumerated in *1. This can be proved in each separate 
--- case, but not generally, because we have no means of specifying (with our 
--- apparatus of primitive ideas) that a function is one which can be built up out 
--- of these ideas alone. We shall give the name of a truth-function to a function 
--- f(p) whose argument is a proposition, and whose truth-value depends only 
--- upon the truth-value of its argument. All the functions of propositions with 
--- which we shall be specially concerned will be truth-functions, i.e. we shall 
--- have p ≡ q . ⊃ . f(p) ≡ f(q).

-- Truth-function preservation under equivalence
theorem truth_function_equiv (p q : Prop) (f : Prop → Prop) : 
  (p ≡ q) → (f p ≡ f q) := by
  intro h
  exact ⟨fun hfp => by rw [← h.2]; exact hfp, fun hfq => by rw [h.1]; exact hfq⟩

/-
Additional theorems from page 0161:
These build on the foundations from Sections 1-3
-/

-- *4.1 ⊢ : p ⊃ q . ≡ . ∼ q ⊃ ∼ p
-- *4.11 ⊢ : p ≡ q . ≡ . ∼ p ≡ ∼ q
-- "These are both forms of the 'principle of transposition.'"
theorem th_4_1 (p q : Prop) : (p → q) ≡ (¬q → ¬p) := by
  constructor
  · exact th_2_16 p q
  · exact th_2_17 p q

theorem th_4_11 (p q : Prop) : (p ≡ q) ≡ (¬p ≡ ¬q) := by
  constructor
  · intro ⟨hpq, hqp⟩
    constructor
    · exact th_2_16 q p hqp
    · exact th_2_16 p q hpq
  · intro ⟨hnqnp, hnpnq⟩
    constructor
    · exact th_2_17 q p hnqnp
    · exact th_2_17 p q hnpnq

-- *4.13 ⊢ . p ≡ ∼ (∼ p)
-- "This is the principle of double negation, i.e. a proposition is equivalent to the falsehood of its negation."
theorem th_4_13 (p : Prop) : p ≡ ¬¬p := by
  constructor
  · intro hp
    intro hnp
    exact hnp hp
  · intro hnnp
    by_contra hnp
    exact hnnp hnp

-- *4.2 ⊢ . p ≡ p
-- *4.21 ⊢ : p ≡ q . ≡ . q ≡ p  
-- *4.22 ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ r
-- "These propositions assert that equivalence is reflexive, symmetrical and transitive."
theorem th_4_2 (p : Prop) : p ≡ p := by
  constructor
  · exact th_2_08 p
  · exact th_2_08 p

theorem th_4_21 (p q : Prop) : (p ≡ q) ≡ (q ≡ p) := by
  constructor
  · intro ⟨hpq, hqp⟩
    exact ⟨hqp, hpq⟩
  · intro ⟨hqp, hpq⟩
    exact ⟨hpq, hqp⟩

theorem th_4_22 (p q r : Prop) : (p ≡ q) ∧ (q ≡ r) → (p ≡ r) := by
  intro ⟨⟨hpq, hqp⟩, ⟨hqr, hrq⟩⟩
  constructor
  · exact fun hp => hqr (hpq hp)
  · exact fun hr => hqp (hrq hr)

-- *4.24 ⊢ : p . ≡ . p . p
-- *4.25 ⊢ : p . ≡ . p ∨ p  
-- "I.e. p is equivalent to 'p and p' and to 'p or p,' which are two forms of the law of tautology"
theorem th_4_24 (p : Prop) : p ≡ (p ∧ p) := by
  constructor
  · intro hp
    exact ⟨hp, hp⟩
  · intro ⟨hp, _⟩
    exact hp

theorem th_4_25 (p : Prop) : p ≡ (p ∨ p) := by
  constructor
  · intro hp
    exact Or.inl hp
  · exact th_1_2 p

-- *4.3 ⊢ : p . q . ≡ . q . p
-- "This is the commutative law for the product of propositions."
theorem th_4_3 (p q : Prop) : (p ∧ q) ≡ (q ∧ p) := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

-- *4.31 ⊢ : p ∨ q . ≡ . q ∨ p
-- "This is the commutative law for the sum of propositions."  
theorem th_4_31 (p q : Prop) : (p ∨ q) ≡ (q ∨ p) := by
  constructor
  · exact th_1_4 p q
  · exact th_1_4 q p

-- *4.71 ⊢ : . p ⊃ q . ≡ : p . ≡ . p . q
-- "I.e. p implies q when, and only when, p is equivalent to p . q."
theorem th_4_71 (p q : Prop) : (p → q) ≡ (p ≡ (p ∧ q)) := by
  constructor
  · intro hpq
    constructor
    · intro hp
      exact ⟨hp, hpq hp⟩
    · intro ⟨hp, _⟩
      exact hp
  · intro ⟨hpconj, hconjp⟩ hp
    exact (hpconj hp).2

-- *4.73 ⊢ : . q . ⊃ : p . ≡ . p . q  
-- "I.e. a true factor may be dropped from or added to a proposition without altering the truth-value of the proposition."
theorem th_4_73 (p q : Prop) : q → (p ≡ (p ∧ q)) := by
  intro hq
  constructor
  · intro hp
    exact ⟨hp, hq⟩
  · intro ⟨hp, _⟩
    exact hp

end Principia.Part1.Section4