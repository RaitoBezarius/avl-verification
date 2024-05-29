import Verification.Rotate
import Verification.Tree
import Verification.AVL
import Verification.Rebalance.BalanceFactor
import Verification.Rebalance.Pure
import Mathlib.Testing.SlimCheck.Sampleable

namespace Implementation

open BST (AVLNode.mk')
open Tree (AVLTree.balancingFactor AVLTree.balancingFactor_eq AVLTree.isAVL AVLNode.left_of_mk AVLNode.right_of_mk AVLNode.val_of_mk)
open Primitives
open avl_verification

attribute [-simp] Bool.exists_bool

-- instance (T: Type) [SlimCheck.SampleableExt T] : SlimCheck.SampleableExt (AVLNode T) :=
--   SlimCheck.SampleableExt.mkSelfContained do
--     let x ← SlimCheck.SampleableExt.interpSample T
--     let y ← SlimCheck.SampleableExt.interpSample (Option (AVLNode T))
--     let z ← SlimCheck.SampleableExt.interpSample (Option (AVLNode T))
--     let h ← SlimCheck.SampleableExt.interpSample Usize
--     pure <| ⟨ x, y, z, h ⟩

mutual
def AVLNode.mirror (self: AVLNode T): AVLNode T := match self with 
| AVLNode.mk x left right h => AVLNode.mk x (AVLTree.mirror right) (AVLTree.mirror left) h

def AVLTree.mirror (self: Tree.AVLTree T): Tree.AVLTree T := match self with 
| none => none
| some t => AVLNode.mirror t
end

@[simp]
def AVLTree.mirror_none: AVLTree.mirror (none: Option (AVLNode T)) = none := by simp [AVLTree.mirror]

@[simp]
lemma AVLNode.mirror_of_mirror (self: Tree.AVLTree T): AVLTree.mirror (AVLTree.mirror self) = self := by
  match self with 
  | none => simp 
  | some t =>
    match t with 
    | AVLNode.mk x left right h =>
      simp [AVLTree.mirror, AVLNode.mirror]
      exact ⟨ AVLNode.mirror_of_mirror _, AVLNode.mirror_of_mirror _ ⟩

@[simp]
lemma AVLNode.height_of_mirror (self: Tree.AVLTree T): Tree.AVLTree.height (AVLTree.mirror self) = Tree.AVLTree.height self := by
  match self with 
  | none => simp
  | some t =>
    match t with 
    | AVLNode.mk x left right h =>
      simp only [AVLTree.mirror, mirror, Tree.AVLTree.height_of_some,
        Tree.AVLTree.height_node_of_mk, add_right_inj]
      rw [AVLNode.height_of_mirror, AVLNode.height_of_mirror]
      simp [max_comm]

@[simp]
lemma AVLTree.height_of_mirror (self: AVLNode T): Tree.AVLTree.height_node (AVLNode.mirror self) = Tree.AVLTree.height_node self := by match self with 
| AVLNode.mk x left right h => simp [AVLNode.mirror, max_comm]

@[simp]
lemma AVLTree.mirror_of_mk' (left right: Tree.AVLTree T): 
  AVLNode.mirror (AVLNode.mk' x left right) = AVLNode.mk' x (AVLTree.mirror right) (AVLTree.mirror left) := by 
  simp [AVLNode.mk', AVLNode.mirror, Scalar.eq_equiv, max_comm]

@[simp]
lemma AVLTree.mirror_of_some (t: AVLNode T):
  AVLTree.mirror (some t) = AVLNode.mirror t := by simp [AVLTree.mirror]

@[simp]
lemma AVLTree.balancingFactor_of_mirror (self: Tree.AVLTree T): AVLTree.balancingFactor (AVLTree.mirror self) = -AVLTree.balancingFactor self := by
  match self with 
  | none => simp [AVLTree.balancingFactor]
  | some t =>
    match t with 
    | AVLNode.mk _ left right _ =>
      simp [AVLTree.mirror, AVLNode.mirror, AVLTree.balancingFactor]

@[simp]
lemma AVLNode.balancingFactor_of_mirror (self: AVLNode T): AVLTree.balancingFactor (some (AVLNode.mirror self)) = -AVLTree.balancingFactor (some self) := by
  match self with 
  | AVLNode.mk _ left right _ => simp [AVLNode.mirror, AVLTree.balancingFactor]

theorem AVLNode.rebalance_mirror_spec (self: AVLNode T):
  AVLNode.rebalance (AVLNode.mirror self) = AVLNode.mirror (AVLNode.rebalance self) := by 
  match self with 
  | AVLNode.mk x left right h =>
    simp only [AVLNode.rebalance, AVLNode.balancingFactor_of_mirror]
    if Hbf : (AVLTree.balancingFactor (some (AVLNode.mk x left right h))) = 2 ∨ (AVLTree.balancingFactor (some (AVLNode.mk x left right h))) = -2 then 
    rcases Hbf with Hbf | Hbf
    all_goals (simp [Hbf])
    . match left with 
      | none => simp [AVLNode.mirror, AVLNode.rotateRight, AVLNode.rotateLeft]
      | some left_node =>
        match left_node with
        | AVLNode.mk y left_left left_right h' =>
          simp [AVLTree.mirror, AVLNode.mirror]
          split_ifs with h₁ h₂ h₃
          all_goals simp only [rotateLeft, rotateRight]
          . rcases left_right with h | h <;> simp_all [AVLTree.mirror]; rcases h with ⟨ lr_x, lr_left, lr_right, lr_h ⟩; simp_all [Scalar.eq_equiv, AVLNode.mirror, AVLTree.mirror, max_comm]
          . rcases left_right with _ | lr
            . simp [AVLTree.mirror, mirror, Scalar.eq_equiv, max_comm]
            . exfalso; rw [← Int.neg_sub, Int.neg_inj] at h₂; exact h₂ h₁
          . rcases left_right with _ | ⟨ lr_x, lr_left, lr_right, lr_h ⟩
            . simp at h₃
            . rcases left_left with _ | ⟨ ll_x, ll_left, ll_right, ll_h ⟩
              . exfalso; apply h₁; simp [Tree.AVLTree.height] at h₃; simp [h₃]
              . exfalso; rw [← Int.neg_sub, Int.neg_inj] at h₃; exact h₁ h₃
          . simp [AVLTree.mirror, mirror, Scalar.eq_equiv, max_comm]
    . match right with 
      | none => simp [AVLNode.mirror, AVLNode.rotateRight, AVLNode.rotateLeft]
      | some right_node =>
        match right_node with
        | AVLNode.mk y right_left right_right h' =>
          simp [AVLTree.mirror, AVLNode.mirror]
          split_ifs with h₁ h₂ h₃
          all_goals simp only [rotateLeft, rotateRight]
          . rcases right_left with _ | rl <;> simp_all [AVLTree.mirror]; rcases rl with ⟨ rl_x, rl_left, rl_right, rl_h ⟩; simp_all only [Tree.AVLTree.height_node_of_mk,
            Nat.cast_add, Nat.cast_one, Nat.cast_max, max_comm, mirror, AVLTree.mirror_of_some,
            AVLNode.mk.injEq, Option.some.injEq, Scalar.eq_equiv, Scalar.ofInt_val_eq,
            height_of_mirror, and_self, Tree.AVLTree.height_of_some]
          . rcases right_left with _ | rl
            . simp [AVLTree.mirror, mirror, Scalar.eq_equiv, max_comm]
            . exfalso; omega
          . rcases right_left with _ | ⟨ rl_x, rl_left, rl_right, rl_h ⟩
            . simp at h₃; omega
            . rcases right_right with _ | ⟨ rr_x, rr_left, rr_right, rr_h ⟩
              . exfalso; apply h₁; simp [Tree.AVLTree.height] at h₃; simp [h₃]
              . exfalso; omega
          . simp only [AVLTree.mirror_of_mk', AVLTree.mirror_of_some]
    else
      rw [mirror]
      push_neg at Hbf
      simp [Hbf]
      split
      . exfalso; simp_all only [Tree.AVLTree.balancingFactor_some, ne_eq]; omega
      . exfalso; simp_all only [Tree.AVLTree.balancingFactor_some, ne_eq]; omega
      . simp_all only [Tree.AVLTree.balancingFactor_some, ne_eq, imp_false, IsEmpty.forall_iff,
        rebalance.match_2.eq_3, mirror]

end Implementation
