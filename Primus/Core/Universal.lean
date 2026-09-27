import Primus.Core.Category
import Primus.Core.Functor
import Primus.Core.Delta
import Primus.Limits.Cone


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
    rw [Fun.compose, ←CC.assoc, f.comm, g.comm]⟩
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
    rw [Fun.compose, CC.assoc, g.comm, f.comm]⟩
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

theorem coneCat_equivalent_overCat{JJ: Cat}(F: Fun JJ CC):
  equivalent (coneCat F) (overCat (deltaFun JJ CC) F)
:= by
  sorry
