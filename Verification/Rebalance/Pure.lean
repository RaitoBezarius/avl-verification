import Verification.Tree
import Verification.Rotate
import Verification.Rebalance.BalanceFactor

namespace Implementation

open BST (AVLNode.mk')
open avl_verification
open Primitives
open Tree (AVLTree.balancingFactor)

def AVLNode.rebalance (self: AVLNode T): AVLNode T := 
match self with 
| AVLNode.mk x left right h =>
  match (AVLTree.balancingFactor (some self)) with 
  | 2 => match left with
    | none => (AVLNode.rotateRight self)
    | some left_node => 
      if AVLTree.balancingFactor (some left_node) = -1 then
        (AVLNode.rotateRight (AVLNode.mk x (AVLNode.rotateLeft left_node) right h))
      else
        (AVLNode.rotateRight self)
  | -2 => match right with 
    | none => (AVLNode.rotateLeft self)
    | some right_node =>
      if AVLTree.balancingFactor (some right_node) = 1 then
        (AVLNode.rotateLeft (AVLNode.mk x left (AVLNode.rotateRight right_node) h))
      else
        (AVLNode.rotateLeft self)
  | _ => self

attribute [-simp] Bool.exists_bool

@[pspec]
theorem AVLNode.rebalance_pure_spec (self: AVLNode T):
  ∃ b t, self.rebalance = .ok (b, t) ∧
    t = AVLNode.rebalance self := by
    simp [avl_verification.AVLNode.rebalance]
    progress with AVLNode.balance_factor_spec as ⟨ bf, Hbf ⟩
    match self with 
    | AVLNode.mk x left right h =>
      split <;> simp only [Result.ok.injEq, Prod.mk.injEq, exists_and_right, exists_eq', true_and]
      . match right with
        | none => 
          exfalso; simp at Hbf
        | some right_node => 
          simp only
          progress with AVLNode.balance_factor_spec as ⟨ rbf, Hlrf ⟩
          split_ifs with Hlrf₁
          . progress with AVLNode.rotate_right_spec' as ⟨ b₁, t₁, H₁ ⟩
            progress with AVLNode.rotate_left_spec' as ⟨ b₂, t₂, H₂ ⟩
            simp at Hbf
            simp [AVLNode.rebalance, Hbf.symm, Hlrf₁, Hlrf.symm, H₂, H₁]
          . progress with AVLNode.rotate_left_spec' as ⟨ b₂, t₂, H₂ ⟩
            simp at Hbf
            simp_all [AVLNode.rebalance, Hbf.symm, Hlrf₁, Hlrf.symm, H₂]
      . match left with
        | none => 
          exfalso; simp at Hbf; linarith
        | some left_node => 
          simp only
          progress with AVLNode.balance_factor_spec as ⟨ rbf, Hlrf ⟩
          split_ifs with Hlrf₁
          . progress with AVLNode.rotate_left_spec' as ⟨ b₁, t₁, H₁ ⟩
            progress with AVLNode.rotate_right_spec' as ⟨ b₂, t₂, H₂ ⟩
            simp at Hbf
            simp [AVLNode.rebalance, Hbf.symm, Hlrf₁, Hlrf.symm, H₂, H₁]
          . progress with AVLNode.rotate_right_spec' as ⟨ b₂, t₂, H₂ ⟩
            simp at Hbf
            simp_all [AVLNode.rebalance, Hbf.symm, Hlrf₁, Hlrf.symm, H₂]
      . simp_all [AVLNode.rebalance, Hbf.symm]

end Implementation
