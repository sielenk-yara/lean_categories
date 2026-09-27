import Primus.Core.Category
import Primus.Core.Functor

@[ext]
structure NaturalTransformation{CC DD: Cat}(F G: Fun CC DD): Sort _ where
  η: (A: CC.Ob) -> DD.Hom (F A) (G A)
  naturality{A B: CC.Ob}(f: CC.Hom A B): η B ≪ F.onHom f = G.onHom f ≪ η A

instance {CC DD: Cat} {F G: Fun CC DD} :
    CoeFun (NaturalTransformation F G) (λ _ => ∀ A : CC.Ob, DD.Hom (F A) (G A)) where
  coe α := α.η

def functorCat(CC DD: Cat): Cat := {
  Ob := Fun CC DD,
  Hom := NaturalTransformation,
  id F := {
    η A := DD.id (F A),
    naturality f := by
      rw [DD.left_id, DD.right_id]
  },
  compose ntG ntF := {
    η A := ntG A ≪ ntF A,
    naturality f := by
      rw [DD.assoc, ←ntG.naturality f, ←DD.assoc, ntF.naturality f, DD.assoc]
    },
  left_id f := by
    simp only [Cat.left_id]
  right_id f := by
    simp only [Cat.right_id]
  assoc h g f := by
    simp
    funext
    rw [DD.assoc]
}
