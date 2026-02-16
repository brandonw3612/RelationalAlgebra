import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra

import Mathlib.Data.Finset.Basic

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/-- Functional dependency over attributes `α`. -/
structure FunctionalDependency (α : Type) where
  lhs : Finset α
  rhs : Finset α
deriving DecidableEq

/-- Notation for functional dependencies. -/
infix:50 " -> " => FunctionalDependency.mk

/-- A functional dependency holds on a relation instance. -/
def FunctionalDependency.holds (fd : FunctionalDependency α) (r : RelationInstance α μ) : Prop :=
  ∀ t₁ t₂, t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ fd.lhs, t₁ a = t₂ a) → (∀ b ∈ fd.rhs, t₁ b = t₂ b)

/-- Trivial dependency: RHS is contained in LHS. -/
def FunctionalDependency.isTrivial (fd : FunctionalDependency α) : Prop :=
  fd.rhs ⊆ fd.lhs

end NF

/-- A relation instance satisfies a set of functional dependencies if it satisfies each dependency in the set. -/
def RelationInstance.satisfies (r : RelationInstance α μ) (F : Finset (NF.FunctionalDependency α)) : Prop :=
  ∀ f ∈ F, f.holds r

end RM
