import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra

import Mathlib.Data.Finset.Basic

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/--
  A decomposition of a relation instance into two subsets of attributes
  whose union covers the entire schema.
-/
structure Decomposition (r : RelationInstance α μ) where
  left : Finset α
  right : Finset α
  cover : left ∪ right = r.schema

/-- The left subset of a decomposition is a subset of the schema. -/
theorem Decomposition.left_subset {r : RelationInstance α μ} (d : Decomposition r) :
  d.left ⊆ r.schema := by
  simp [← d.cover]

/-- The right subset of a decomposition is a subset of the schema. -/
theorem Decomposition.right_subset {r : RelationInstance α μ} (d : Decomposition r) :
  d.right ⊆ r.schema := by
  simp [← d.cover]

/-- A decomposition is lossless if the original relation can be reconstructed by joining the projections on the left and right subsets. -/
def Decomposition.isLossless {r : RelationInstance α μ} (d : Decomposition r) : Prop :=
  r = join (projection r d.left d.left_subset) (projection r d.right d.right_subset)

end NF

namespace RM
