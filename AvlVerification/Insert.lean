import AvlVerification.Tree
import AvlVerification.BinarySearchTree
import AvlVerification.Specifications

namespace Implementation

open Primitives
open avl_verification
open Tree (AVLTree)

variable {T: Type}

@[pspec]
theorem AVLTreeSet.insert_loop_spec {H: avl_verification.Ord T} 
  (a: T) (t: Option (AVLNode T))
  [LT T]
  (Hbs_search: BST.BST t)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o):
  ∃ added t_new, AVLTreeSet.insert_loop T H a t = Result.ret ⟨ added, t_new ⟩
--  ∧ AVLTree.set t'.2 = insert a (AVLTree.set t)
  ∧ BST.BST t_new
  := by match t with
  | none =>
    simp [AVLTreeSet.insert_loop, AVLTree.set, setOf, BST.BST]
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals simp only []
    have Hbs_search_right: BST.BST right := BST.right Hbs_search
    have Hbs_search_left: BST.BST left := BST.left Hbs_search
    {
      progress keep Htree as ⟨ added₁, right₁, Hbst ⟩
      refine' ⟨ added₁, ⟨ some (AVLNode.mk b left right₁), _ ⟩ ⟩
      simp only [true_and]
      refine' (BST.BST.some b left right₁ _ _ Hbs_search_left Hbst)
      cases' Hbs_search; assumption
      induction right with
      | none =>
        simp [AVLTreeSet.insert_loop] at Htree
        rw [← Htree.2]
        refine' (BST.ForallNode.some _ _ _ BST.ForallNode.none _ BST.ForallNode.none)
        sorry
      | some node =>
        -- clef: ∀ x ∈ node.right, b < x
        -- de plus: b < a
        -- or, right₁ = insert a node.right moralement
        -- donc, il suffit de prouver que: ∀ x ∈ insert a node.right, b < x <-> b < a /\ ∀ x ∈ node.right, b < x
        sorry
    }
    {
      simp [Hbs_search]
    }
    {
      -- Symmetric case of left.
      sorry
    }

@[pspec]
def AVLTreeSet.insert_spec 
  {H: avl_verification.Ord T} 
  -- TODO: this can be generalized into `H.cmp` must be an equivalence relation.
  -- and insert works no longer on Sets but on set quotiented by this equivalence relation.
  (Hcmp_eq: ∀ a b, H.cmp a b = Result.ret Ordering.Equal -> a = b)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o)
  (Hbs_search: @BSTree.searchInvariant _ H t)
  (a: T) (t: AVLTreeSet T):
  ∃ t', t.insert _ H a = Result.ret t' 
  -- set of values *POST* insertion is {a} \cup set of values of the *PRE* tree.
  ∧ AVLTree.setOf t'.2.root = insert a (AVLTree.setOf t.root) 
  -- it's still a binary search tree.
  ∧ @BSTree.searchInvariant _ H t'.2.root
  -- TODO(reinforcement): (t'.1 is false <=> a \in AVLTree.setOf t.root)
  := by
  rw [AVLTreeSet.insert]
  progress keep h as ⟨ t', Hset ⟩; simp
  rw [Hset]
  sorry


-- insert is infaillible, right?
-- instance [LT T] (o: avl_verification.Ord T): Insert T (AVLTreeSet T) where
--   insert x tree := (AVLTreeSet.insert T o tree x).map (fun (added, tree) => tree)

end Implementation

