import Verification.Tree
import Verification.AVL
import Verification.Extracted
import Verification.Height
import Verification.BinarySearchTree

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLNode.memoized_height AVLNode.val AVLNode.right AVLNode.left AVLTree.balancingFactor)
open Primitives
open avl_verification

variable (T: Type) (H: avl_verification.Ord T) [LinearOrder T] (Ospec: OrdSpecLinearOrderEq H)

@[pspec]
theorem AVLNode.rotate_right_spec (self: AVLNode T):
  ∃ rotated t_new, self.rotate_right = .ok (rotated, t_new) 
  ∧ ((AVLNode.left self).isNone -> rotated = false ∧ t_new = AVLNode.mk (AVLNode.val self) none (AVLNode.right self) (AVLNode.memoized_height self))
  ∧ ((AVLNode.left self) = .some self_left -> rotated = true
    ∧ t_new = 
      AVLNode.mk' (AVLNode.val self_left) (AVLNode.left self_left) 
        (AVLNode.mk' (AVLNode.val self) (AVLNode.right self_left) (AVLNode.right self))
    )
  := by 
  match self with 
  | AVLNode.mk a left right memoized_height => 
    match left with 
    | .none => simp [AVLNode.rotate_right, AVLNode.left, AVLNode.val, AVLNode.right, AVLNode.memoized_height]
    | .some (AVLNode.mk b left_left left_right h) => 
      simp only [AVLNode.rotate_right, Option.isNone_some, not_false_eq_true, neq_imp, ↓reduceIte,
        core.mem.replace, Option.take, core.mem.swap, Bool.exists_bool]
      right
      -- TODO: why it doesn't unify without `this`
      -- this is very weird -- Son
      have := AVLNode.update_height_spec a h left_right right
      progress keep Hupdate₁ with AVLNode.update_height_spec as ⟨ t_new₁, H₁ ⟩
      progress keep Hupdate₂ with AVLNode.update_height_spec as ⟨ t_new, H₂ ⟩
      simp [AVLNode.left]
      intro Hleft
      simp [← Hleft, H₂, H₁, AVLNode.val, AVLNode.right]

@[pspec]
theorem AVLNode.rotate_left_spec (self: AVLNode T):
  ∃ rotated t_new, self.rotate_left = .ok (rotated, t_new)
  ∧ ((AVLNode.right self).isNone -> rotated = false ∧ t_new = AVLNode.mk (AVLNode.val self) (AVLNode.left self) none (AVLNode.memoized_height self))
  ∧ ((AVLNode.right self) = .some self_right -> rotated = true
    ∧ t_new = 
      AVLNode.mk' (AVLNode.val self_right) 
        (AVLNode.mk' (AVLNode.val self) (AVLNode.left self) (AVLNode.left self_right))
        (AVLNode.right self_right)
    )
  := by
  match self with 
  | AVLNode.mk a left right memoized_height => 
    match right with 
    | .none => simp [AVLNode.rotate_left, AVLNode.right, AVLNode.val, AVLNode.left, AVLNode.memoized_height]
    | .some (AVLNode.mk b right_left right_right h) => 
      simp only [AVLNode.rotate_left, Option.isNone_some, not_false_eq_true, neq_imp, ↓reduceIte,
        core.mem.replace, Option.take, core.mem.swap, Bool.exists_bool]
      right
      -- TODO: why it doesn't unify without `this`
      -- this is very weird -- Son
      have := AVLNode.update_height_spec a h right_right right
      progress keep Hupdate₁ with AVLNode.update_height_spec as ⟨ t_new₁, H₁ ⟩
      progress keep Hupdate₂ with AVLNode.update_height_spec as ⟨ t_new, H₂ ⟩
      simp [AVLNode.right]
      intro Hright
      simp [← Hright, H₂, H₁, AVLNode.val, AVLNode.left]


end Implementation
