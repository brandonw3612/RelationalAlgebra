import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep

import Mathlib.Data.Finset.Basic

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/-- Superkey: equality on `K` implies equality on the whole schema. -/
def is_superkey (K : Finset α) (R : Finset α) : Prop :=
  ∀ {μ} {r : RelationInstance α μ} {t₁ t₂}, r.schema = R → t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ K, t₁ a = t₂ a) → (∀ a ∈ R, t₁ a = t₂ a)

/-- Candidate key: minimal superkey of which no strict subset is a superkey. -/
def is_candidate_key (K : Finset α) (R : Finset α) : Prop :=
  is_superkey K R ∧
  ∀ K' ⊂ K, ¬ is_superkey K' R

end NF

end RM
