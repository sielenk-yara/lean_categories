import Primus.Core.Category
import Primus.Core.Functor


variable {JJ CC: Cat}


@[ext]
structure ConeOb(F: Fun JJ CC): Sort _ where
  N: CC.Ob
  π J : CC.Hom N (F J)
  comm{J₁ J₂}: ∀(f: JJ.Hom J₁ J₂), F.onHom f ≪ π J₁ = π J₂

attribute [simp] ConeOb.comm


@[ext]
structure ConeHom{F}(X Y: @ConeOb JJ CC F): Sort _ where
  h: CC.Hom X.N Y.N
  fac: ∀J, Y.π J ≪ h = X.π J

attribute [simp] ConeHom.fac


def coneCat(F: Fun JJ CC): Cat := {
  Ob := ConeOb F,
  Hom := ConeHom,
  id X := ⟨CC.id X.N, by
    intro J
    rw [CC.right_id]
  ⟩
  compose g f := ⟨g.h ≪ f.h, by
    intro J
    rw [CC.assoc, g.fac, f.fac]
  ⟩
  left_id f := by
    simp only [Cat.left_id]
  right_id f := by
    simp only [Cat.right_id]
  assoc h g f := by
    simp only [Cat.assoc]
}

@[simp] theorem coneCatOb {F: Fun JJ CC}: ConeOb F = (coneCat F).Ob  := rfl
@[simp] theorem coneCatHom{F: Fun JJ CC}: ConeHom  = (coneCat F).Hom := rfl
