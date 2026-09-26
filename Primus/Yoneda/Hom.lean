import Primus.Core.Category
import Primus.Core.Opposite
import Primus.Core.Functor
import Primus.Core.NatTrans
import Primus.Instances.SortCat


def homFun.{m, n}{CC: Cat.{m, n}}(X: CC.Ob): Fun (op CC) sortCat.{n} := {
  onOb := (op CC).Hom X,
  onHom := (op CC).compose,
  id{A} := by
    funext h
    simp [sortCat]
  compose{A B C g f} := by
    funext h
    simp [sortCat]
    rw [CC.assoc]
}


def yonedaDown{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Hom (NaturalTransformation (homFun X) F) (F X)
:=
  fun nt => nt X (CC.id X)

def yonedaUp{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Hom (F X) (NaturalTransformation (homFun X) F)
:=
  fun x => {
    η Y f := F.onHom f x,
    naturality{A B} f := by
      funext g
      simp [sortCat, homFun]
      rw [@F.compose _ _ _ f g]
      simp [sortCat]
  }

theorem yoneda{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  isomorphic (NaturalTransformation (homFun X) F) (F X)
:= by
  refine ⟨yonedaDown F X, ?_⟩
  refine ⟨yonedaUp F X, ?_⟩
  simp [sortCat, yonedaDown, yonedaUp]
  funext ⟨η, H1⟩; simp [homFun] at η H1
  congr
  funext Y f; simp
  apply @Eq.trans _ _ ((λ x ↦ η Y (x ≪ f)) (CC.id X))
  rw [H1 f]
  simp
  rw [CC.left_id f]

def yonedaEmbedding(CC: Cat):
  Fun CC (functorCat (op CC) sortCat)
:= {
  onOb := homFun
  onHom {C D} h := {
    η C := CC.compose h
    naturality := by
      simp [sortCat, homFun]
      intro B A f
      funext g
      apply CC.assoc
  }
  id := by
    simp [functorCat, sortCat, homFun, natTransId]
    intro A
    congr
    funext B f
    simp
  compose := by
    simp [functorCat, sortCat, homFun, natTransComp]
    intro B C D h g
    congr
    funext A f
    rw [CC.assoc]
}

theorem yoneda_fully_faithful(CC: Cat):
  fullyFaithful (yonedaEmbedding CC)
:= by
  constructor
  · intros X Y nt
    refine ⟨nt.η X (CC.id X), ?_⟩
    simp [yonedaEmbedding]
    congr
    funext Z f
    let g: CC.Hom X X → CC.Hom Z Y := λ h ↦ (nt.η X h) ≪ f
    have H1 : (λ h ↦ nt.η Z (h ≪ f)) = g := nt.naturality f
    change g (CC.id X) = _
    rw [←H1]
    simp
    eq_refl
  · intro X Y f1 f2 H1
    let ye := yonedaEmbedding CC
    let nt₁ := (ye.onHom f1)
    let nt₂ := (ye.onHom f2)
    change nt₁ = nt₂ at H1
    have H2: nt₁.η X (CC.id X) = nt₂.η X (CC.id X) := by rw [H1]
    simp [nt₁, nt₂, ye, yonedaEmbedding] at H2
    assumption
