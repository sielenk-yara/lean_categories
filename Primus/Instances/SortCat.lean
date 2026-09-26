import Primus.Core.Category
import Primus.Core.Functor
import Primus.Diagrams.Discrete
import Primus.Diagrams.Two
import Primus.Diagrams.EqualizerDiagram
import Primus.Diagrams.PullbackDiagram

import Mathlib.Data.Set.Image


def sortCat.{m}: Cat.{m+1, m} := {
  Ob := Sort m,
  Hom A B :=  A -> B,
  id _ x := x,
  compose g f x := g (f x)
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def sortCat.initial: InitialObject sortCat := {
  I := PEmpty
  hom X := fun e => PEmpty.elim e
  unique X g := by
    funext x
    cases x
}

def sortCat.terminal: TerminalObject sortCat := {
  T := PUnit
  hom X := fun _ => PUnit.unit
  unique X g := by
    funext x
    cases g x
    rfl
}

def obToHom{A: sortCat.Ob}(x: A): sortCat.Hom sortCat.terminal A :=
  fun _ => x

theorem obToHom_injective(A: sortCat.Ob): Function.Injective (@obToHom A) := by
  intro x1 x2 H1
  exact congrFun H1 PUnit.unit

theorem obToHom_surjective(A: sortCat.Ob): Function.Surjective (@obToHom A) := by
  intro f
  exists (f PUnit.unit)

theorem sort_mono_injective{A B: sortCat.Ob}(f: sortCat.Hom A B):
  mono f ↔ Function.Injective f :=
by
  constructor
  · intro H1 x1 x2 H2
    rw [←@obToHom_injective A x1 x2]
    apply H1
    funext t
    assumption
  · intro H1 X g1 g2 H2
    funext x
    apply H1
    have H3: f (g1 x) = (f ≪ g1) x := by rfl
    rw [H3, H2]
    rfl

theorem sort_epi_surjective{A B: sortCat.{m+1}.Ob}(f: sortCat.Hom A B):
  epi f ↔ Function.Surjective f :=
by
  constructor
  · intro Hepi b
    let g1: sortCat.Hom B _ := fun b' => ULift.up True
    let g2: sortCat.Hom B _ := fun b' => ULift.up (∃a, f a = b')
    change (g2 b).down
    have Heq: g1 = g2 := by
      apply Hepi
      funext a'
      simp [sortCat, g1, g2]
      exact ⟨a', rfl⟩
    rw [←Heq]
    exact True.intro
  · intro Hsurj C g1 g2 Heq1
    funext b
    have ⟨a, Heq2⟩ := Hsurj b
    rw [←Heq2]
    change (g1 ≪ f) a = (g2 ≪ f) a
    rw [Heq1]

theorem sort_split_epi_surjective{A B: sortCat.Ob}(f: sortCat.Hom A B):
  splitEpi f ↔ Function.Surjective f :=
by
  constructor
  · intro ⟨g, H1⟩ b
    use (g b)
    have H2: f (g b) = (f ≪ g) b := by rfl
    rw [H2, H1]
    rfl
  · intro H1
    use (fun b => Classical.choose (H1 b))
    funext b
    unfold sortCat; simp
    exact Classical.choose_spec (H1 b)

theorem sort_split_epi_epi.{m}{A B: sortCat.{m+1}.Ob}(f: sortCat.Hom A B):
  epi f → splitEpi f :=
by
  rw [sort_split_epi_surjective, ←sort_epi_surjective]
  tauto


def sortCat.Equalizer{X Y: sortCat.Ob}(f₁ f₂: sortCat.Hom X Y): Equalizer f₁ f₂ :=
  {
    T := {
      N := { x // f₁ x = f₂ x }
      π J := match J with
        | EqualizerOb.A => Subtype.val
        | EqualizerOb.B => λX => f₁ X.val
      comm f := match f with
        | EqualizerHom.idA => sortCat.left_id _
        | EqualizerHom.idB => sortCat.left_id _
        | EqualizerHom.f₁ => rfl
        | EqualizerHom.f₂ => funext (λ N => Eq.symm N.property)
    }
    hom X := {
      h x := ⟨
        X.π EqualizerOb.A x,
         Eq.trans
          (congrArg (λ h => h x) (X.comm EqualizerHom.f₁))
          (Eq.symm
            (congrArg (λ h => h x) (X.comm EqualizerHom.f₂))
          )
      ⟩
      fac J := match J with
        | EqualizerOb.A => rfl
        | EqualizerOb.B => X.comm EqualizerHom.f₁
    }
    unique _ g :=
      ConeHom.ext (funext (λ_ => Subtype.ext (congr_fun (g.fac EqualizerOb.A) _)))
  }

def sortCat.Pullback{X₁ X₂ Y: sortCat.Ob}
  (f₁: sortCat.Hom X₁ Y)(f₂: sortCat.Hom X₂ Y): Pullback f₁ f₂ :=
by
  refine {
    T := {
      N := { xx: X₁ × X₂ // f₁ xx.1 = f₂ xx.2 }
      π J X := match J with
        | PullbackOb.A₁ => X.val.1
        | PullbackOb.A₂ => X.val.2
        | PullbackOb.B => f₁ X.val.1
      comm f := match f with
        | PullbackHom.idA₁ => sortCat.left_id _
        | PullbackHom.idA₂ => sortCat.left_id _
        | PullbackHom.idB => sortCat.left_id _
        | PullbackHom.f₁ => rfl
        | PullbackHom.f₂ => funext (λ N => Eq.symm N.property)
    }
    hom X := {
      h x := ⟨
        ⟨X.π PullbackOb.A₁ x, X.π PullbackOb.A₂ x⟩,
        Eq.trans
          (congrArg (λ h => h x) (X.comm PullbackHom.f₁))
          (Eq.symm
            (congrArg (λ h => h x) (X.comm PullbackHom.f₂))
          )
      ⟩
      fac J := match J with
        | PullbackOb.A₁ => rfl
        | PullbackOb.A₂ => rfl
        | PullbackOb.B => X.comm PullbackHom.f₁
    }
    unique X g := ?unique
  }
  · case unique =>
    apply ConeHom.ext
    funext x
    apply Subtype.ext
    apply Prod.ext
    · apply congrArg (λ h => h x) (g.fac PullbackOb.A₁)
    · apply congrArg (λ h => h x) (g.fac PullbackOb.A₂)

def sortCat.Lim{JJ: Cat}(F: Fun JJ sortCat): Lim F :=
  {
    T := {
      N := { X // ∀{J₁ J₂} f, F.onHom f (X J₁) = X J₂ }
      π J := by
        intro ⟨X, _⟩
        exact X J
      comm {J₁ J₂} f := by
        funext X
        exact X.property f
    }
    hom X := {
      h x := ⟨
        fun J => X.π J x,
        by
          intro J₁ J₂ f
          simp
          rw [←X.comm f]
          rfl
      ⟩
      fac J := rfl
    }
    unique X := by
      intro ⟨h', fac'⟩
      congr
      funext x
      ext J
      simp [←fac' J, sortCat]
  }
