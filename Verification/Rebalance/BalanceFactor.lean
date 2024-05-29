import Verification.Rotate
import Verification.Tree
import Verification.AVL

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLTree.balancingFactor AVLTree.balancingFactor_eq AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification


@[pspec]
theorem AVLNode.balance_factor_spec (self: AVLNode T):
  ∃ f, self.balance_factor = .ok f ∧ f.val = AVLTree.balancingFactor (some self) := by 
  match self with 
  | AVLNode.mk x left right h =>
    rcases left with _ | left <;> rcases right with _ | right <;> simp [AVLNode.balance_factor, AVLNode.left_height_spec, AVLNode.right_height_spec]
    . simp [AVLNode.left_height, AVLNode.right_height]
      progress as ⟨ y, Hy ⟩
      simp at Hy
      use 0#i8
      -- TODO: (0#usize) as i8 = .ok 0#i8
      sorry
    . simp [AVLNode.left_height]
      progress
      . sorry
      . 
        -- ¬ (0 ≤ x) is impossible.
        split_ifs <;> sorry
    . progress
      . sorry
      . simp [AVLNode.right_height]
        split_ifs <;> sorry
    . progress as ⟨ hl, Hleft ⟩
      . sorry
      . progress as ⟨ hr, Hright ⟩
        . sorry
        . split_ifs <;> progress as ⟨ z, Hz ⟩ <;> sorry

end Implementation
