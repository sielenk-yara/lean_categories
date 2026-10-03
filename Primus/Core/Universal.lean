import Primus.Core.Category
import Primus.Core.Functor
import Primus.Core.Delta
import Primus.Limits.Cone
import Primus.Core.IsoFun


variable {CC DD: Cat}


/-! Not `commaCat (delta one X) G`: spelling `X` as a functor out of `one` leaves
    `one`'s two universe levels unconstrained, so they survive as junk parameters
    and trip `checkUnivs`. -/


@[ext]
structure UnderOb(X: CC.Ob)(G: Fun DD CC): Sort _ where
  B: DD.Ob
  h: CC.Hom X (G B)

@[ext]
structure UnderHom{X: CC.Ob}{G: Fun DD CC}(P Q: UnderOb X G): Sort _ where
  f: DD.Hom P.B Q.B
  comm: G.onHom f ≪ P.h = Q.h

attribute [simp] UnderHom.comm

def underCat(X: CC.Ob)(G: Fun DD CC): Cat := {
  Ob := UnderOb X G
  Hom := UnderHom
  id P := ⟨DD.id P.B, by simp⟩
  compose g f := ⟨g.f ≪ f.f, by
    rw [Fun.preserves_compose, ←CC.assoc, f.comm, g.comm]⟩
  left_id f := by ext; simp
  right_id f := by ext; simp
  assoc h g f := by ext; apply DD.assoc
}


@[ext]
structure OverOb(G: Fun DD CC)(X: CC.Ob): Sort _ where
  B: DD.Ob
  h: CC.Hom (G B) X

@[ext]
structure OverHom{G: Fun DD CC}{X: CC.Ob}(P Q: OverOb G X): Sort _ where
  f: DD.Hom P.B Q.B
  comm: Q.h ≪ G.onHom f = P.h

attribute [simp] OverHom.comm

def overCat(G: Fun DD CC)(X: CC.Ob): Cat := {
  Ob := OverOb G X
  Hom := OverHom
  id P := ⟨DD.id P.B, by simp⟩
  compose g f := ⟨g.f ≪ f.f, by
    rw [Fun.preserves_compose, CC.assoc, g.comm, f.comm]⟩
  left_id f := by ext; simp
  right_id f := by ext; simp
  assoc h g f := by ext; apply DD.assoc
}


/-! `underCat`/`overCat` are plain `def`s, so `simp` cannot see through them at
    reducible transparency: a lemma stated over `UnderOb` rather than
    `(underCat X G).Ob` is silently never tried. -/

@[simp] theorem underCatOb{X: CC.Ob}{G: Fun DD CC}: UnderOb X G = (underCat X G).Ob := rfl
@[simp] theorem underCatHom{X: CC.Ob}{G: Fun DD CC}: UnderHom = (underCat X G).Hom := rfl

@[simp] theorem underCat_id_f{X: CC.Ob}{G: Fun DD CC}(P: (underCat X G).Ob):
  ((underCat X G).id P).f = DD.id P.B
:= rfl

@[simp] theorem underCat_compose_f{X: CC.Ob}{G: Fun DD CC}{P Q R: (underCat X G).Ob}
  (g: (underCat X G).Hom Q R)(f: (underCat X G).Hom P Q):
  ((underCat X G).compose g f).f = g.f ≪ f.f
:= rfl

@[simp] theorem overCatOb{G: Fun DD CC}{X: CC.Ob}: OverOb G X = (overCat G X).Ob := rfl
@[simp] theorem overCatHom{G: Fun DD CC}{X: CC.Ob}: OverHom = (overCat G X).Hom := rfl

@[simp] theorem overCat_id_f{G: Fun DD CC}{X: CC.Ob}(P: (overCat G X).Ob):
  ((overCat G X).id P).f = DD.id P.B
:= rfl

@[simp] theorem overCat_compose_f{G: Fun DD CC}{X: CC.Ob}{P Q R: (overCat G X).Ob}
  (g: (overCat G X).Hom Q R)(f: (overCat G X).Hom P Q):
  ((overCat G X).compose g f).f = g.f ≪ f.f
:= rfl


abbrev UniversalMorphism(X: CC.Ob)(G: Fun DD CC) :=
  InitialObject (underCat X G)

abbrev CoUniversalMorphism(G: Fun DD CC)(X: CC.Ob) :=
  TerminalObject (overCat G X)

abbrev Lim'{JJ: Cat}(F: Fun JJ CC) :=
  CoUniversalMorphism (deltaFun JJ CC) F


def isoFun_coneCat_overCat{JJ: Cat}(F: Fun JJ CC):
  IsoFun (coneCat F) (overCat (deltaFun JJ CC) F)
:= {
  F := {
    onOb A := by
      refine ⟨A.N, A.π, ?_⟩
      intros J₁ J₂ f
      change _ ≪ CC.id A.N = _
      rw [CC.right_id, ←A.comm f]
      rfl

    onHom := by
      intro A B f
      refine ⟨f.h, ?_⟩
      apply NaturalTransformation.ext
      change (B.π · ≪ f.h) = A.π
      funext J
      apply f.fac

    preserves_id := by
      intro A
      apply OverHom.ext
      rfl

    preserves_compose := by
      intros A B C g f
      apply OverHom.ext
      rfl

  }

  G := {
    onOb A := by
      refine ⟨A.B, λ J => A.h.η J, ?comm⟩
      intros J₁ J₂ f
      let g₁: CC.Hom A.B _ := F.onHom f ≪ A.h.η J₁
      let g₂: CC.Hom A.B _ := A.h.η J₂
      have H1 := A.h.naturality f
      change g₂ ≪ CC.id _ = g₁ at H1
      change g₁ = g₂
      rw [←H1, CC.right_id]

    onHom := by
      intro A B f
      refine ⟨f.f, ?_⟩
      have H1 : B.h ≪ _ = A.h := f.comm
      change ∀ J, B.h.η J ≪ f.f = A.h.η J
      intros J
      rw [←H1]
      rfl

    preserves_id := by
      intro A
      apply ConeHom.ext
      rfl

    preserves_compose := by
      intros A B C g f
      apply ConeHom.ext
      rfl
  }

  GF_is_id := by
    apply Fun.ext
    intro A
    rfl
    intro A B f
    rfl

  FG_is_id := by
    apply Fun.ext
    intro A
    rfl
    intro A B f
    rfl
}
