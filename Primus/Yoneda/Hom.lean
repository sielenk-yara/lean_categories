import Primus.Core.Category
import Primus.Core.Opposite
import Primus.Core.Functor
import Primus.Core.NatTrans
import Primus.Instances.SortCat


def homFun.{m, n}{CC: Cat.{m, n}}(X: CC.Ob): Fun (op CC) sortCat.{n} := {
  onOb := (op CC).Hom X,
  onHom := (op CC).compose,
  preserves_id{A} := by
    funext h
    simp only [Cat.right_id, sortCat]
  preserves_compose{A B C g f} := by
    funext h
    exact CC.assoc h f g
}


def yonedaDown{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Hom (NaturalTransformation (homFun X) F) (F X)
:=
  λnt => nt X (CC.id X)

def yonedaUp{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Hom (F X) (NaturalTransformation (homFun X) F)
:=
  λ x => {
    η Y f := F.onHom f x,
    naturality{A B} f := by
      funext g
      simp only [sortCat, homFun]
      rw [@F.preserves_compose _ _ _ f g]
      simp only [sortCat]
  }

def yoneda{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Iso (NaturalTransformation (homFun X) F) (F X)
:= by
  refine ⟨yonedaDown F X, yonedaUp F X, ?down, ?up⟩
    <;> simp only [sortCat, yonedaDown, yonedaUp, Fun.preserves_id]
  funext ⟨η, H⟩; simp [homFun] at η H
  ext A f
  show (λ x => F.onHom f (η X x)) (CC.id X) = η A f
  rw [←H f]
  simp only
  rw [CC.left_id f]

def yonedaEmbedding CC:
  Fun CC (functorCat (op CC) sortCat)
:= {
  onOb := homFun
  onHom {C D} h := {
    η C := CC.compose h
    naturality := by
      simp only [sortCat, homFun, Cat.assoc, implies_true]
  }
  preserves_id := by
    simp only [sortCat, functorCat, homFun]
    intro A
    congr
    funext B f
    simp only [Cat.left_id]
  preserves_compose := by
    simp [functorCat, sortCat, homFun]
    intro B C D h g
    congr
    funext A f
    simp only
    rw [CC.assoc]
}

theorem yonedaEmbedding.is_faithful CC:
  faithful (yonedaEmbedding CC)
:= by
  intro X Y f1 f2 H1
  let ye := yonedaEmbedding CC
  let nt₁ := ye.onHom f1
  let nt₂ := ye.onHom f2
  change nt₁ = nt₂ at H1
  have H2: nt₁.η X (CC.id X) = nt₂.η X (CC.id X) := by rw [H1]
  simp only [yonedaEmbedding, Cat.right_id, ye, nt₁, nt₂] at H2
  assumption

theorem yonedaEmbedding.is_full CC:
  full (yonedaEmbedding CC)
:= by
  intros X Y nt
  refine ⟨nt.η X (CC.id X), ?_⟩
  simp only [yonedaEmbedding]
  congr
  funext Z f
  let g: CC.Hom X X → CC.Hom Z Y := λ h ↦ (nt.η X h) ≪ f
  have H1 : (λ h ↦ nt.η Z (h ≪ f)) = g := nt.naturality f
  show g (CC.id X) = _
  rw [←H1]
  simp only [Cat.left_id]
  eq_refl

theorem yonedaEmbedding.is_fullyFaithful(CC: Cat):
  fullyFaithful (yonedaEmbedding CC)
:= by
  and_intros
  . apply yonedaEmbedding.is_full
  . apply yonedaEmbedding.is_faithful
