import Verification.Extracted
import Verification.Tree
import Verification.BinarySearchTree

namespace Implementation

variable {T: Type}

open avl_verification
open Primitives
open Tree (AVLTree AVLNode.left AVLNode.right AVLTree.height_node AVLNode.memoized_height)
open BST (AVLNode.mk')

variable (t: AVLNode T) [O: LinearOrder T] (Tcopy: core.marker.Copy T) (H: avl_verification.Ord T)

@[pspec]
def max_spec {a b: T}: ∃ o, avl_verification.max _ H Tcopy a b = .ok o ∧ o = O.max a b := sorry

@[pspec]
def AVLNode.left_height_spec
  (left: AVLNode T): (AVLNode.mk x (some left) right h).left_height = left.height
  := by simp only [AVLNode.left_height]

@[pspec]
def AVLNode.right_height_spec
  (right: AVLNode T): (AVLNode.mk x left (some right) h).right_height = right.height
  := by simp only [AVLNode.right_height]

-- TODO:
-- * bound discharge
-- * recursion call for the last case
-- * stuck proofs.
@[pspec]
def AVLNode.height_spec
  [InBounds .Usize (AVLTree.height_node (AVLNode.mk x left right h))]: (AVLNode.mk x left right h).height = .ok (Scalar.ofInt $ AVLTree.height_node (AVLNode.mk x left right h))
  := by
  simp [AVLNode.height]
  cases left <;> simp [AVLNode.left_height]
  cases right <;> simp [AVLNode.right_height]
  progress with max_spec
  -- stuck term on AVLTree.height_node
  sorry
  rename (AVLNode _) => left
  cases left
  progress
  . sorry -- inbounds
  . progress with max_spec
    -- stuck simplification which is almost reflexivity
    sorry
  rename (AVLNode _) => left
  cases left
  sorry
--  progress <-- this progress will cause a structural recursion issue because it will call back this very specification.
--  . sorry -- inbounds
--  . cases right <;> simp [AVLNode.right_height]
--    any_goals progress with max_spec
--    -- previous proof with right_left.
--    sorry
--    sorry

-- Under bounds, we keep the bounds?
@[pspec]
def AVLNode.update_height_spec (x: T) (h: Usize) (left right: AVLTree T): ∃ t_new, AVLNode.update_height _ (AVLNode.mk x left right h) = .ok t_new ∧ t_new = AVLNode.mk' x left right := sorry

end Implementation
