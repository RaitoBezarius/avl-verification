import Verification.Tree
import Verification.BinarySearchTree
import Verification.Specifications
import AvlVerification

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree AVLTree.set)
open Specifications (OrdSpecLinearOrderEq infallible ltOfRustOrder gtOfRustOrder)

variable (T: Type) (H: avl_verification.Ord T) [DecidableEq T] [LinearOrder T] (Ospec: OrdSpecLinearOrderEq H)

@[pspec]
def AVLTreeSet.find_loop_spec
  (a: T) (t: Option (AVLNode T)):
  BST.Invariant t -> a ∈ AVLTree.set t -> AVLTreeSet.find_loop _ H a t = Result.ok true := fun Hbst Hmem => by
  match t with 
  | none => trivial
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.find_loop]
    dsimp only
    have : ∀ a b, ∃ o, H.cmp a b = .ok o := infallible H
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals dsimp only
    . refine' AVLTreeSet.find_loop_spec a right (BST.right Hbst) (BST.right_pos Hbst Hmem _)
      exact ltOfRustOrder _ _ _ Hordering
    . refine' AVLTreeSet.find_loop_spec a left (BST.left Hbst) (BST.left_pos Hbst Hmem _)
      exact gtOfRustOrder _ _ _ Hordering

def AVLTreeSet.find_spec
  (a: T) (t: AVLTreeSet T):
  BST.Invariant t.root -> a ∈ AVLTree.set t.root ->
    t.find _ H a = Result.ok true := fun Hbst Hmem => by
    rw [AVLTreeSet.find]; progress

end Implementation

