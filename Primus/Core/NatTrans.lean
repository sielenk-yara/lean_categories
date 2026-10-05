import Primus.Core.Category
import Primus.Core.Functor

@[ext]
structure NaturalTransformation{CC DD: Cat}(F G: Fun CC DD): Sort _ where
  η: (A: CC.Ob) -> DD.Hom (F A) (G A)
  naturality{A B: CC.Ob}(f: CC.Hom A B): η B ≪ F.onHom f = G.onHom f ≪ η A

instance {CC DD: Cat} {F G: Fun CC DD} :
    CoeFun (NaturalTransformation F G) (λ _ => ∀ A : CC.Ob, DD.Hom (F A) (G A)) where
  coe α := α.η


@[ext]
structure NaturalIso{CC DD: Cat}(F G: Fun CC DD): Sort _ where
  η: (A: CC.Ob) -> DD.Iso (F A) (G A)
  naturality{A B}(f: CC.Hom A B): (η B).f ≪ F.onHom f = G.onHom f ≪ (η A).f

instance {CC DD: Cat} {F G: Fun CC DD} :
    CoeFun (NaturalIso F G) (λ _ => ∀ A : CC.Ob, DD.Iso (F A) (G A)) where
  coe α := α.η

def NaturalIso.inverse{CC DD: Cat}{F G: Fun CC DD}:
  NaturalIso F G -> NaturalIso G F
:= by
  intro nt
  refine ⟨λ A => (nt.η A).inverse, ?_⟩
  intros A B f
  let i₁ := (nt.η A).inverse
  let i₂ := (nt.η B).inverse
  have H1 : i₂.g ≪ _ = _ ≪ i₁.g := nt.naturality f
  change i₂.f ≪ G.onHom f = F.onHom f ≪ i₁.f
  have H3 : i₂.g ≪ i₂.f ≪ G.onHom f ≪ i₁.g = i₂.g ≪ F.onHom f ≪ i₁.f ≪ i₁.g := by
    rw [H1, i₂.gf_is_id, DD.left_id, ←DD.assoc, i₁.fg_is_id, DD.right_id]
  apply i₂.inverse.is_mono
  apply i₁.inverse.is_epi
  change i₂.g ≪ _≪ i₁.g = i₂.g ≪ _ ≪ i₁.g
  rw [DD.assoc, H3, DD.assoc]


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
