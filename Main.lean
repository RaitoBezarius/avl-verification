import «AvlVerification»
open Primitives

namespace Avl

-- synthesize inhabited?
-- synthesize type aliases
-- AVLTree T := Option<Box<AVLNode>> ~ AVLTree T := Option<AVLNode>

open avl_verification
variable {T: Type}

def AVL.nil: AVLTreeSet T := { root := none }


-- TODO: AVLTree T ou AVLNode T?
noncomputable def AVL.height' (tree: AVLNode T): Nat := AVLNode.rec tree
  (mk := fun _ _ _ ihl ihr => 1 + ihl + ihr)
  (none := 0)
  (some := fun _ ih => 1 + ih)

-- Otherwise, Lean cannot prove termination by itself.
@[reducible]
def AVLTree (U: Type) := Option (AVLNode U)

mutual
def AVL.height'' (tree: AVLNode T): Nat := match tree with
| AVLNode.mk y left right => 1 +  AVL.height left + AVL.height right

def AVL.height (tree: AVLTree T): Nat := match tree with 
| none => 0
| some node => 1 + AVL.height'' node
end


@[reducible]
def AVLTree.mem (tree: AVLTree T) (x: T) :=
  match tree with
  | none => False
  | some (AVLNode.mk y left right) => x = y ∨ AVLTree.mem left x ∨ AVLTree.mem right x

@[simp]
def AVLTree.mem_none: AVLTree.mem none = ({}: Set T) := rfl

-- TODO: why the explicit type annotation is required here?
-- TODO(reinforcement): ∪ is actually disjoint.
@[simp]
def AVLTree.mem_some {x: T} {left right: AVLTree T}: AVLTree.mem (some (AVLNode.mk x left right)) = (({x}: Set T) ∪ AVLTree.mem left ∪ AVLTree.mem right) := by
  ext y
  rw [AVLTree.mem]
  simp [Set.insert_union]
  simp [Set.insert_def, Set.setOf_set, Set.mem_def, Set.union_def]


def AVLTree.setOf: AVLTree T -> Set T := AVLTree.mem
def AVLTree.val (t: AVLTree T): Option T := match t with
| none => none
| some (AVLNode.mk x _ _) => some x
def AVLTree.left (t: AVLTree T): AVLTree T := match t with
| none => none
| some (AVLNode.mk _ left _) => left
def AVLTree.right (t: AVLTree T): AVLTree T := match t with
| none => none
| some (AVLNode.mk _ _ right) => right

def AVLTree.mem_eq_setOf (t: AVLTree T): AVLTree.mem t = t.setOf := rfl

-- TODO: {t.val} = {} if t.val is none else {t.val.get!} otherwise.
-- @[simp]
-- def AVLTree.setOf_eq_union (t: AVLTree T): t.setOf = {t.val} ∪ t.left.setOf ∪ t.right.setOf := sorry

-- Note: we would like to have a theorem that says something like
-- t.setOf = {t.val} ∪ t.left.setOf ∪ t.right.setOf
-- but it's not doable because Aeneas does not generate a `structure` but an inductive type with one constructor.

#check AVL.nil
#check U32.ofInt 0
#check 0#u32
-- TODO: créer une instance OfNat pour les Uxyz.
-- TODO: générer {} adéquatement... ?
-- TODO: derive from Ord an Lean Order instance.
-- TODO: oh no, H.cmp returns a Result!

@[pspec]
theorem AVLTreeSet.insert_loop_spec {H: avl_verification.Ord T} 
  (a: T) (t: Option (AVLNode T))
  (Hcmp_eq: ∀ a b, H.cmp a b = Result.ret Ordering.Equal -> a = b)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o):
  ∃ t', AVLTreeSet.insert_loop T H a t = Result.ret t' 
  ∧ AVLTree.setOf t'.2 = insert a (AVLTree.setOf t) := by match t with
  | none =>
    simp [AVLTreeSet.insert_loop, AVLTree.setOf]
  | some (AVLNode.mk b left right) =>
    rw [AVLTreeSet.insert_loop]
    simp only []
    progress keep Hordering as ⟨ ordering ⟩
    cases ordering
    all_goals {
      -- TODO: oof.
      -- We are trying to tackle all goals at the same time.
      -- Refactor this to make it only one simp ideally without even `try`.
      simp only []
      try progress keep H as ⟨ t'', Hset ⟩
      simp [AVLTree.setOf]
      try simp [AVLTree.setOf] at Hset
      try simp [Hset]
      try rw [Set.insert_comm, Set.insert_union]
      try simp [Hcmp_eq _ _ Hordering]
    }

@[pspec]
def AVLTreeSet.insert_spec 
  {H: avl_verification.Ord T} 
  -- TODO: this can be generalized into `H.cmp` must be an equivalence relation.
  -- and insert works no longer on Sets but on set quotiented by this equivalence relation.
  (Hcmp_eq: ∀ a b, H.cmp a b = Result.ret Ordering.Equal -> a = b)
  (Hcmp_spec: ∀ a b, ∃ o, H.cmp a b = Result.ret o)
  (a: T) (t: AVLTreeSet T):
  ∃ t', t.insert _ H a = Result.ret t' 
  -- set of values *POST* insertion is {a} \cup set of values of the *PRE* tree.
  ∧ AVLTree.setOf t'.2.root = insert a (AVLTree.setOf t.root) 
  -- TODO(reinforcement): (t'.1 is false <=> a \in AVLTree.setOf t.root)
  := by
  rw [AVLTreeSet.insert]
  progress keep h as ⟨ t', Hset ⟩; simp
  rw [Hset]

end Avl
