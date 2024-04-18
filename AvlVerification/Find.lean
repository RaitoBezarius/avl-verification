import AvlVerification.Tree
import AvlVerification.BinarySearchTree
import AvlVerification.Specifications

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree AVLTree.set)
open Specifications (OrdSpecDualityEq ordOfOrdSpec ltOfRustOrder gtOfRustOrder)

variable (T: Type) (H: avl_verification.Ord T) (Ospec: @OrdSpecDualityEq T H)

@[pspec]
def AVLTreeSet.find_loop_spec
  (a: T) (t: Option (AVLNode T)):
  BST.Invariant t -> a ∈ AVLTree.set t -> AVLTreeSet.find_loop _ H a t = Result.ok true := fun Hbst Hmem => by
  match t with 
  | none => trivial
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.find_loop]
    dsimp only
    have : ∀ a b, ∃ o, H.cmp a b = .ok o := Ospec.infallible
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals dsimp only
    . refine' AVLTreeSet.find_loop_spec a right (BST.right Hbst) _
      -- b < a
      -- Hbst fournit que a ∈ right
      sorry
    . refine' AVLTreeSet.find_loop_spec a left (BST.left Hbst) _
      -- symmétrie du précédent.
      sorry

def AVLTreeSet.find_spec
  (a: T) (t: AVLTreeSet T):
  BST.Invariant t.root -> a ∈ AVLTree.set t.root ->
    t.find _ H a = Result.ok true := fun Hbst Hmem => by
    rw [AVLTreeSet.find]; progress

end Implementation

