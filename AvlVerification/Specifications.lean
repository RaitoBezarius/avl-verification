import «AvlVerification»

namespace Primitives

namespace Result

def map {A B: Type} (x: Result A) (f: A -> B): Result B := match x with
| .ret y => .ret (f y)
| .fail e => .fail e
| .div => .div

@[inline]
def isRet {A: Type} : Result A -> Bool
| .ret _ => true
| .fail _ => false
| .div => false

@[inline]
def get? {A: Type}: (r: Result A) -> isRet r -> A
| .ret x, _ => x

end Result

end Primitives

namespace avl_verification

def Ordering.toLeanOrdering (o: avl_verification.Ordering): _root_.Ordering := match o with 
| .Less => .lt
| .Equal => .eq
| .Greater => .gt

end avl_verification

namespace Specifications

open Primitives
open Result

variable {T: Type} (H: avl_verification.Ord T)

class OrdSpec where
  cmp: T -> T -> Result Ordering := fun x y => (H.cmp x y).map (fun z => z.toLeanOrdering)
  infallible: ∀ a b, ∃ (o: Ordering), cmp a b = .ret o

@[simp]
theorem OrdSpec.cmpEq {Spec: OrdSpec H}: ∀ x y, Spec.cmp x y = (H.cmp x y).map (fun z => z.toLeanOrdering) := sorry

@[simp]
theorem OrdSpec.infallibleEq {Spec: OrdSpec H}: ∀ a b, ∃ (o: Ordering), Spec.cmp a b = .ret o <-> ∀ a b, ∃ (o: Ordering), (H.cmp a b).map (fun z => z.toLeanOrdering) = .ret o := sorry

instance: Coe (avl_verification.Ordering) (_root_.Ordering) where
  coe a := a.toLeanOrdering

def ordSpecOfInfaillible
  (H: avl_verification.Ord T)
  (Hresult: ∀ a b, ∃ o, H.cmp a b = Primitives.Result.ret o)
  : OrdSpec H where
  infallible := by
    intros a b; cases' (Hresult a b) with o Hcmp; refine' ⟨ o.toLeanOrdering, _ ⟩
    simp [Result.map, Hcmp]

def ordOfOrdSpec (H: avl_verification.Ord T) (spec: OrdSpec H): Ord T where
  compare x y := (spec.cmp x y).get? (by
    cases' (spec.infallible x y) with o Hcmp
    rewrite [isRet, Hcmp]
    simp only
  )

end Specifications
