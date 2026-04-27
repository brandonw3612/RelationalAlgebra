import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep

import Mathlib.Data.Finset.Basic

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/--
  A decomposition of a schema into two subsets of attributes
  whose union covers the entire schema.
-/
structure Decomposition (R : Finset α) where
  left : Finset α
  right : Finset α
  cover : left ∪ right = R

/-- The left subset of a decomposition is a subset of the schema. -/
theorem Decomposition.left_subset {R : Finset α} {d : Decomposition R} {r : RelationInstance α μ} :
  r.schema = R → d.left ⊆ r.schema := by
  intro h_r
  simp [← d.cover, h_r]

/-- The right subset of a decomposition is a subset of the schema. -/
theorem Decomposition.right_subset {R : Finset α} {d : Decomposition R} {r : RelationInstance α μ} :
  r.schema = R → d.right ⊆ r.schema := by
  intro h_r
  simp [← d.cover, h_r]

/-- A decomposition is lossless if the original relation can be reconstructed by joining the projections on the left and right subsets. -/
def Decomposition.is_lossless {R : Finset α} (d : Decomposition R) (F : Finset (FunctionalDependency α)) : Prop :=
  ∀ {μ : Type} (r : RelationInstance α μ),
    (h_r : r.schema = R) → r.satisfies F →
    r = join (projection r d.left (d.left_subset h_r)) (projection r d.right (d.right_subset h_r))

inductive DecompositionTree : Finset α → Type where
  | leaf (R : Finset α) : DecompositionTree R
  | node {R : Finset α} (d : Decomposition R)
    (left : DecompositionTree d.left) (right : DecompositionTree d.right) : DecompositionTree R

def DecompositionTree.leaves {R : Finset α} : DecompositionTree R → Finset (Finset α)
  | DecompositionTree.leaf R => {R}
  | DecompositionTree.node _ left right => left.leaves ∪ right.leaves

def DecompositionTree.is_lossless {R : Finset α} : DecompositionTree R → Finset (FunctionalDependency α) → Prop
  | .leaf _, _ => True
  | .node d left right, F => d.is_lossless F ∧ left.is_lossless F ∧ right.is_lossless F

end NF

namespace RM
