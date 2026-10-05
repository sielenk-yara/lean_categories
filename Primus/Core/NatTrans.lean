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


def NaturalIso.toNaturalTransformation{CC DD: Cat}{F G: Fun CC DD}:
  NaturalIso F G -> NaturalTransformation F G
:= by
  intro nt
  refine ⟨λ A => (nt.η A).f, ?_⟩
  intros A B f
  apply nt.naturality


def NaturalTransformation.id{CC DD: Cat}(F: Fun CC DD):
  NaturalTransformation F F
:= {
  η A := DD.id (F A),
  naturality f := by
    rw [DD.left_id, DD.right_id]
}

def NaturalTransformation.compose{CC DD: Cat}{F G H: Fun CC DD}:
  NaturalTransformation G H -> NaturalTransformation F G -> NaturalTransformation F H
:=
  λ ntG ntF => {
    η A := ntG A ≪ ntF A,
    naturality f := by
      rw [DD.assoc, ←ntG.naturality f, ←DD.assoc, ntF.naturality f, DD.assoc]
  }

def functorCat(CC DD: Cat): Cat := {
  Ob := Fun CC DD,
  Hom := NaturalTransformation,
  id := NaturalTransformation.id,
  compose := NaturalTransformation.compose,
  left_id f := by
    simp only [NaturalTransformation.compose, NaturalTransformation.id, DD.left_id]
  right_id f := by
    simp only [NaturalTransformation.compose, NaturalTransformation.id, DD.right_id]
  assoc h g f := by
    simp only [NaturalTransformation.compose, DD.assoc]
}


def NaturalIso.toIso{CC DD: Cat}{F G: Fun CC DD}(n: NaturalIso F G): (functorCat CC DD).Iso F G := {
  f := ⟨λ A => (n.η A).f, n.naturality⟩
  g := ⟨λ A => (n.η A).g, n.inverse.naturality⟩
  gf_is_id := by apply NaturalTransformation.ext; funext A; exact (n.η A).gf_is_id
  fg_is_id := by apply NaturalTransformation.ext; funext A; exact (n.η A).fg_is_id
}

def NaturalIso.ofIso{CC DD: Cat}{F G: Fun CC DD}(i: (functorCat CC DD).Iso F G): NaturalIso F G := {
  η A := ⟨i.f.η A, i.g.η A, by
    change (i.g ≪ i.f).η A = _
    rw [i.gf_is_id]
    rfl
  , by
    change (i.f ≪ i.g).η A = _
    rw [i.fg_is_id]
    rfl
  ⟩
  naturality := i.f.naturality
}


theorem NaturalIso.toIso_ofIso{CC DD: Cat}{F G: Fun CC DD}(i: (functorCat CC DD).Iso F G):
  toIso (ofIso i) = i
:= by
  apply Cat.Iso.ext
  apply NaturalTransformation.ext
  funext A
  rfl

theorem NaturalIso.ofIso_toIso{CC DD: Cat}{F G: Fun CC DD}(n: NaturalIso F G):
  ofIso n.toIso = n
:= by
  apply NaturalIso.ext
  funext A
  rfl
