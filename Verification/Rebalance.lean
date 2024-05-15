import Verification.Rotate
import Verification.Tree
import Verification.AVL

namespace Implementation

open Tree (AVLTree.balancingFactor AVLTree.isAVL)
open Primitives
open avl_verification

@[pspec]
theorem AVLNode.rebalance_spec (self: AVLNode T):
  (AVLTree.balancingFactor (some self)) = 2 ∨ (AVLTree.balancingFactor (some self)) = -2 
  -> ∃ t_new, self.rebalance = .ok (true, t_new)
      ∧ AVLTree.isAVL (some t_new) := by
      sorry


end Implementation
