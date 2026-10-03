import Primus.Core.Category


def prodCat(CC DD: Cat): Cat := {
  Ob := CC.Ob × DD.Ob,
  Hom X Y := CC.Hom X.1 Y.1 × DD.Hom X.2 Y.2,
  id X := (CC.id X.1, DD.id X.2),
  compose g f:= (g.1 ≪ f.1, g.2 ≪ f.2),
  left_id f := by
    simp only [Cat.left_id]
  right_id f := by
    simp only [Cat.right_id]
  assoc h g f:= by
    simp only [Cat.assoc]
}
