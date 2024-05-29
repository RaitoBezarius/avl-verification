import Verification.Rotate
import Verification.Tree
import Verification.AVL

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLTree.balancingFactor AVLTree.balancingFactor_eq AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification

lemma AVLTree.structure_of_nonzero_height (t: Tree.AVLTree T): 1 ≤ Tree.AVLTree.height t -> ∃ x left right h, t = some (AVLNode.mk x left right h) := by
  intro Ht
  match t with 
  | none => simp [Tree.AVLTree.height] at Ht
  | some (AVLNode.mk x left right h) => refine' ⟨ x, left, right, h, rfl ⟩

lemma AVLTree.left_structure_of_nonzero_bf (t: Tree.AVLTree T): 1 ≤ AVLTree.balancingFactor t -> ∃ x left right h, t = some (AVLNode.mk x (some left) right h) := by 
  intro Ht
  match t with 
  | none => simp [Tree.AVLTree.balancingFactor] at Ht
  | some (AVLNode.mk x none right h) => 
    simp [Tree.AVLTree.balancingFactor, Tree.AVLTree.height] at Ht; linarith [Ht]
  | some (AVLNode.mk x (some left) right h) => refine' ⟨ x, left, right, h, rfl ⟩

lemma AVLTree.right_structure_of_nonzero_bf (t: Tree.AVLTree T): AVLTree.balancingFactor t ≤ -1 -> ∃ x left right h, t = some (AVLNode.mk x left (some right) h) := by 
  intro Ht
  match t with 
  | none => simp [Tree.AVLTree.balancingFactor] at Ht
  | some (AVLNode.mk x left none h) => 
    simp [Tree.AVLTree.balancingFactor, Tree.AVLTree.height] at Ht; linarith [Ht]
  | some (AVLNode.mk x left (some right) h) => refine' ⟨ x, left, right, h, rfl ⟩

lemma AVLTree.left_height_of_bf {left: AVLNode T}: AVLTree.balancingFactor (some left) ≥ 0 -> Tree.AVLTree.height (some left) = 1 + Tree.AVLTree.height (Tree.AVLNode.left left) := by 
  intro Hlbf
  match left with 
  | AVLNode.mk x left_left left_right h => 
    simp [AVLTree.balancingFactor] at Hlbf 
    simp [Tree.AVLTree.height, Hlbf]

end Implementation
