import Primus.Core.Category
import Primus.Core.Functor


variable {AA BB CC: Cat}
variable (S: Fun AA CC)
variable (T: Fun BB CC)

structure CommaOb: Sort _ where
  A: AA.Ob
  B: BB.Ob
  h: CC.Hom (S A) (T B)

structure CommaHom(X Y: CommaOb S T): Sort _ where
  f: AA.Hom X.A Y.A
  g: BB.Hom X.B Y.B
  comm: Y.h ≪ S.onHom f = T.onHom g ≪ X.h

def commaCat: Cat := {
  Ob := CommaOb S T,
  Hom := CommaHom S T,
  id X := ⟨AA.id X.A, BB.id X.B, by simp⟩
  compose g f := ⟨g.f ≪ f.f, g.g ≪ f.g, by
    simp
    rw [CC.assoc, g.comm, ← CC.assoc, ← CC.assoc, f.comm]
  ⟩
  left_id f := by
    simp only [Cat.left_id]
  right_id f := by
    simp only [Cat.right_id]
  assoc h g f := by
    simp
    and_intros
    apply AA.assoc
    apply BB.assoc
}

@[simp] theorem commaCatOb: CommaOb S T = (commaCat S T).Ob := rfl
@[simp] theorem commaCatHom: CommaHom S T = (commaCat S T).Hom := rfl
