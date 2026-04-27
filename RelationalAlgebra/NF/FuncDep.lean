import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra

import Mathlib.Data.Finset.Basic

import Architect

namespace RM

variable {α μ : Type} [DecidableEq α]

namespace NF

/-- Functional dependency over attributes of type `α`. -/
@[
  blueprint "definition:fd"
  (title := /-- Functional Dependency -/)
  (statement := /--
    A functional dependency over attributes of type $\alpha$ is a pair of
    finite sets of attributes, \textit{lhs} and \textit{rhs},
    denoted as \textit{lhs} $\rightarrow$ \textit{rhs}.
  -/)
]
structure FunctionalDependency (α : Type) where
  lhs : Finset α
  rhs : Finset α
deriving DecidableEq

/-- Notation for functional dependencies. -/
infix:50 " -> " => FunctionalDependency.mk

/-- A functional dependency holds on a relation instance. -/
@[
  blueprint "definition:fd-holds"
  (title := /-- FD Holds -/)
  (statement := /--
    A functional dependency holds on a relation instance if, for any two tuples
    in the relation instance, their agreement on all attributes of the left-hand side (lhs)
    strictly implies their agreement on all attributes of the right-hand side (rhs).
  -/)
]
def FunctionalDependency.holds (fd : FunctionalDependency α) (r : RelationInstance α μ) : Prop :=
  ∀ {t₁ t₂}, t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ fd.lhs, t₁ a = t₂ a) → (∀ b ∈ fd.rhs, t₁ b = t₂ b)

/-- Trivial functional dependency: RHS is contained in LHS. -/
@[
  blueprint "definition:trivial-fd"
  (title := /-- Trivial FD -/)
  (statement := /--
    A functional dependency is trivial if its right-hand side (rhs) is contained
    in its left-hand side (lhs).
  -/)
]
def FunctionalDependency.is_trivial (fd : FunctionalDependency α) : Prop :=
  fd.rhs ⊆ fd.lhs

end NF

/-- A relation instance satisfies a set of functional dependencies
    if it satisfies each dependency in the set. -/
@[
  blueprint "definition:relation-satisfies-fds"
  (title := /-- Relation Satisfies FD Set -/)
  (statement := /--
    A relation instance $r$ satisfies a set of functional dependencies
    if each dependency in the set holds on $r$.
  -/)
]
def RelationInstance.satisfies (r : RelationInstance α μ) (F : Finset (NF.FunctionalDependency α)) : Prop :=
  ∀ {f}, f ∈ F → f.holds r

end RM

namespace Finset

variable {α : Type} [DecidableEq α]

/-- A set of attributes `S` is closed under a set of FDs `F` if,
    for every functional dependency `X -> Y ∈ F`,
    if `X ⊆ S`, then `Y ⊆ S`.
-/
def is_closed_under (S : Finset α) (F : Finset (RM.NF.FunctionalDependency α)) : Prop :=
  ∀ fd ∈ F, fd.lhs ⊆ S → fd.rhs ⊆ S

end Finset
