import Verification.Rotate
import Verification.Tree
import Verification.AVL
import Verification.Rebalance.BalanceFactor
import Verification.Rebalance.Pure
import Verification.Rebalance.Basic
import Verification.Rebalance.Mirror

namespace Implementation

open Tree (AVLTree.balancingFactor AVLTree.balancingFactor_eq AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification

lemma AVLTree.isAVL.mirror: AVLTree.isAVL t ↔ AVLTree.isAVL (AVLTree.mirror t) := by 
  simp [AVLTree.isAVL]

@[pspec]
theorem AVLNode.rebalance_spec (self: AVLNode T):
  AVLTree.isAVL (Tree.AVLNode.left self) -> AVLTree.isAVL (Tree.AVLNode.right self) -> (AVLTree.balancingFactor (some self)) = 2 ∨ (AVLTree.balancingFactor (some self)) = -2 
  -> ∃ t_new, self.rebalance = .ok (true, t_new)
      ∧ AVLTree.isAVL (some t_new) := by
      intro H_avl_left H_avl_right
      rintro (H_balancing | H_balancing)
      . match self with 
        | AVLNode.mk x left right h => 
          exact AVLNode.rebalance_spec_positive _ _ H_avl_left H_avl_right H_balancing
      -- BF = -2.
      . -- Mirror mirror argument time!
        match self with 
        | AVLNode.mk x left right h =>
          progress with AVLNode.rebalance_pure_spec as ⟨ b, t, Ht ⟩
          -- obtain ⟨ t_new, Htnew ⟩ := AVLNode.rebalance_spec_positive (AVLTree.mirror right) (AVLTree.mirror left) (AVLTree.isAVL.mirror.1 H_avl_right) (AVLTree.isAVL.mirror.1 H_avl_left) (by simp [H_balancing, AVLTree.balancingFactor_of_mirror]; sorry)
          -- TODO: lift everything to pure beforehand, lift rebalance_spec_positive to pure land.
          -- just use commutativity rule.
          -- use (AVLNode.mirror t_new)
          -- AVLNode.rebalance_mirror_spec
          sorry



end Implementation
