import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra

import Mathlib.Data.Finset.Basic

namespace RM

variable {α μ : Type} [DecidableEq α]

namespace NF

/-- Functional dependency over attributes `α`. -/
structure FunctionalDependency (α : Type) where
  lhs : Finset α
  rhs : Finset α
deriving DecidableEq

/-- Notation for functional dependencies. -/
infix:50 " -> " => FunctionalDependency.mk

/-- A functional dependency holds on a relation instance. -/
def FunctionalDependency.holds (fd : FunctionalDependency α) (r : RelationInstance α μ) : Prop :=
  ∀ {t₁ t₂}, t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ fd.lhs, t₁ a = t₂ a) → (∀ b ∈ fd.rhs, t₁ b = t₂ b)

/-- A functional dependency holds on a schema if it holds on all relation instances with that schema. -/
def FunctionalDependency.holds_on_schema (fd : FunctionalDependency α) (R : Finset α) : Prop :=
  ∀ {μ : Type} {r : RelationInstance α μ}, r.schema = R → fd.holds r

/-- Trivial dependency: RHS is contained in LHS. -/
def FunctionalDependency.is_trivial (fd : FunctionalDependency α) : Prop :=
  fd.rhs ⊆ fd.lhs

end NF

/-- A relation instance satisfies a set of functional dependencies if it satisfies each dependency in the set. -/
def RelationInstance.satisfies (r : RelationInstance α μ) (F : Finset (NF.FunctionalDependency α)) : Prop :=
  ∀ f ∈ F, f.holds r

def schema_satisfies (R : Finset α) (F : Finset (NF.FunctionalDependency α)) : Prop :=
  ∀ {μ : Type} {r : RelationInstance α μ}, r.schema = R → r.satisfies F

end RM

namespace Finset

variable {α : Type} [DecidableEq α]

def is_closed_under (S : Finset α) (F : Finset (RM.NF.FunctionalDependency α)) : Prop :=
  ∀ fd ∈ F, fd.lhs ⊆ S → fd.rhs ⊆ S

end Finset
