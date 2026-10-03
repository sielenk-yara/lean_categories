import Primus.Core.Category
import Primus.Core.Functor


variable {JJ CC: Cat}


@[ext]
structure CoConeOb(F: Fun JJ CC): Sort _ where
  N: CC.Ob
  π J : CC.Hom (F J) N
  comm{J₁ J₂}(f: JJ.Hom J₁ J₂): π J₂ ≪ F.onHom f = π J₁

attribute [simp] CoConeOb.comm


@[ext]
structure CoConeHom{F}(X Y: @CoConeOb JJ CC F): Sort _ where
  h: CC.Hom X.N Y.N
  fac J: h ≪ (X.π J) = Y.π J

attribute [simp] CoConeHom.fac


def coConeCat(F: Fun JJ CC): Cat := {
  Ob := CoConeOb F,
  Hom := CoConeHom,
  id X := ⟨CC.id X.N, by
    intro J
    rw [CC.left_id]
  ⟩
  compose g f := ⟨g.h ≪ f.h, by
    intro J
    rw [←CC.assoc, f.fac, g.fac]
  ⟩
  left_id f := by
    simp only [Cat.left_id]
  right_id f := by
    simp only [Cat.right_id]
  assoc h g f := by
    simp only [Cat.assoc]
}

@[simp] theorem coConeCatOb {F: Fun JJ CC}: CoConeOb F = (coConeCat F).Ob  := rfl
@[simp] theorem coConeCatHom{F: Fun JJ CC}: CoConeHom  = (coConeCat F).Hom := rfl
