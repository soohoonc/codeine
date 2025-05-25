/-
SECTION 2: IMMEDIATE CONSEQUENCES OF THE PRIMITIVE PROPOSITIONS

From pages 0143-0144 of Principia Mathematica

"The proofs of the earlier of the propositions of this number consist simply
in noticing that they are instances of the general rules given in *1. In such
cases, these rules are not premises, since they assert any instance of themselves, not something other than their instances. Hence when a general rule
is adduced in early proofs, it will be adduced in brackets."

This section derives the immediate logical consequences that follow directly
from the primitive propositions established in Section 1.
-/

import Mathlib.Logic.Basic
import Principia.Section1

namespace Principia.Part1.Section2

open Principia.Part1.Section1

/-
From page 0144: "∗2·02. ⊢ : q . ⊃ . p ⊃ q"
"I.e. q implies that p implies q, i.e. a true proposition is implied by any
proposition. This proposition is called the 'principle of simplification' (referred to as 'Simp'), because, as will appear later, it enables us to pass from
the joint assertion of q and p to the assertion of q simply."
-/
theorem th_2_02 (p q: Prop) : q → (p → q) := by
  intro hq _
  exact hq

/-
From page 0144: "∗2·03. ⊢ : p ⊃ ∼ q . ⊃ . q ⊃ ∼ p"
∗2·15. ⊢ : ∼ q ⊃ p . ⊃ . ∼ p ⊃ q  
∗2·16. ⊢ : p ⊃ q . ⊃ . ∼ q ⊃ ∼ p
∗2·17. ⊢ : ∼ q ⊃ ∼ p . ⊃ . p ⊃ q

"These four analogous propositions constitute the 'principle of transposition,'
referred to as 'Transp.' They lead to the rule that in an implication the two
sides may be interchanged by turning negative into positive and positive into
negative. They are thus analogous to the algebraical rule that the two sides
of an equation may be interchanged by changing the signs."
-/
theorem th_2_03 (p q: Prop) : (p → ¬q) → (q → ¬p) := by
  intro h hq
  intro hp
  exact h hp hq

theorem th_2_15 (p q: Prop) : (¬q → p) → (¬p → q) := by
  intro h hnp
  by_contra hnq
  have hp := h hnq
  exact hnp hp

theorem th_2_16 (p q: Prop) : (p → q) → (¬q → ¬p) := by
  intro h hnq
  intro hp
  exact hnq (h hp)

theorem th_2_17 (p q: Prop) : (¬q → ¬p) → (p → q) := by
  intro h hp
  by_contra hnq
  exact h hnq hp

/-
From page 0144: "∗2·04. ⊢ : . p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r"
"This is called the 'commutative principle' and referred to as 'Comm.'
It states that, if r follows from q provided p is true, then r follows from p
provided q is true."
-/
theorem th_2_04 (p q r: Prop) : (p → (q → r)) → (q → (p → r)) := by
  intro h hq hp
  exact h hp hq

/-
From page 0144: "∗2·05. ⊢ : . q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r"
∗2·06. ⊢ : . p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r

"These two propositions are the source of the syllogism in Barbara (as will
be shown later) and are therefore called the 'principle of the syllogism'
(referred to as 'Syll'). The first states that, if r follows from q, then if q
follows from p, r follows from p. The second states the same thing with the
premisses interchanged."
-/
theorem th_2_05 (p q r: Prop) : (q → r) → ((p → q) → (p → r)) := by
  intro hqr hpq hp
  exact hqr (hpq hp)

theorem th_2_06 (p q r: Prop) : (p → q) → ((q → r) → (p → r)) := by
  intro hpq hqr hp
  exact hqr (hpq hp)

/-
From page 0144: "∗2·08. ⊢ . p ⊃ p"
"I.e. any proposition implies itself. This is called the 'principle of identity'
and referred to as 'Id.' It is not the same as the 'law of identity' ('a is
identical with a'), but the law of identity is inferred from it (cf. ∗13·15)."
-/
theorem th_2_08 (p: Prop) : p → p := by
  intro hp
  exact hp

/-
From page 0144: "∗2·21. ⊢ : ∼ p . ⊃ . p ⊃ q"
"I.e. a false proposition implies any proposition."
-/
theorem th_2_21 (p q: Prop) : ¬p → (p → q) := by
  intro hnp hp
  exfalso
  exact hnp hp

end Principia.Part1.Section2