import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra

import Mathlib.Data.Finset.Basic

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/-- Superkey: equality on `K` implies equality on the whole schema. -/
def is_superkey (r : RelationInstance α μ) (K : Finset α) : Prop :=
  K ⊆ r.schema ∧
  ∀ t₁ t₂, t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ K, t₁ a = t₂ a) → (∀ a ∈ r.schema, t₁ a = t₂ a)

/-- Candidate key: minimal superkey of which no strict subset is a superkey. -/
def is_candidate_key (r : RelationInstance α μ) (K : Finset α) : Prop :=
  is_superkey r K ∧
  ∀ K' ⊂ K, ¬ is_superkey r K'

end NF

end RM
