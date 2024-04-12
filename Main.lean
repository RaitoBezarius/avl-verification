import «AvlVerification»
open Primitives

namespace Avl

-- synthesize inhabited?
-- synthesize type aliases
-- AVLTree T := Option<Box<AVLNode>> ~ AVLTree T := Option<AVLNode>

open avl_verification
variable {T: Type}

-- instance {H: avl_verification.Ord T}: LT T := {
--  lt := λ x y => H.cmp x y = Result.ret Ordering.Less
-- }

-- This is the binary search invariant.
def BSTree.searchInvariant {H: avl_verification.Ord T} (t: AVLTree T) := match t with
| none => True
| some (AVLNode.mk y u v) => ∀ x ∈ AVLTree.setOf (u : AVLTree T), H.cmp y x = Result.ret Ordering.Less ∧ ∀ x ∈ AVLTree.setOf (v : AVLTree T), H.cmp y x = Result.ret Ordering.Greater

-- Prove that:
-- searchInvariant t <-> searchInvariant t.left /\ searchInvariant t.right /\ something about t.val
-- searchInvariant t -> searchInvariant t.left /\ searchInvariant t.right by weakening.

def BSTree.nil_has_searchInvariant {H: avl_verification.Ord T}: @BSTree.searchInvariant _ H AVL.nil.root := by trivial

theorem BSTree.searchInvariant_children {H: avl_verification.Ord T} (t: AVLTree T): @searchInvariant _ H t -> @searchInvariant _ H t.left ∧ @searchInvariant _ H t.right := sorry

def AVLTree.height (t: AVLTree T) := AVL.height t
def AVLTree.balanceFactor (t: AVLTree T): Int := t.right.height - t.left.height
def AVLTree.balanceInvariant (t: AVLTree T) := t.balanceFactor = -1 ∨ t.balanceFactor = 0 ∨ t.balanceFactor = 1

def AVLTree.mem_eq_setOf (t: AVLTree T): AVLTree.mem t = t.setOf := rfl

end Avl
