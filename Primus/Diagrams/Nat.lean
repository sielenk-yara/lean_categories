import Primus.Core.Category
import Primus.Diagrams.EqualizerDiagram
import Primus.Diagrams.PullbackDiagram


def natCat: Cat.{1, 0} := {
  Ob := Nat
  Hom := Nat.le
  id _ := Nat.le.refl
  compose g f := Nat.le_trans f g
  left_id _ := rfl
  right_id _:= rfl
  assoc _ _ _ := rfl
}

def natCat.initial: InitialObject natCat :=
  {
    I := Nat.zero
    hom := Nat.zero_le
    unique _ _ := rfl
  }

theorem natCat.is_mono{A B: natCat.Ob}(f: natCat.Hom A B): mono f :=
  λ _ => rfl

def natCat.equalizer{A B: natCat.Ob}(f₁ f₂: natCat.Hom A B): Equalizer f₁ f₂ :=
  Equalizer.mk f₁ f₂ A (natCat.id A)
    rfl
    (λ m _ => ⟨m, rfl⟩)
    (natCat.is_mono (natCat.id A))

def natCat.pullback{A₁ A₂ B: natCat.Ob}
  (f₁: natCat.Hom A₁ B)(f₂: natCat.Hom A₂ B): Pullback f₁ f₂
:=
  {
    T := {
      N := Nat.min A₁ A₂
      π J := match J with
        | PullbackOb.A₁ => Nat.min_le_left A₁ A₂
        | PullbackOb.A₂ => Nat.min_le_right A₁ A₂
        | PullbackOb.B => Nat.le_trans (Nat.min_le_left A₁ A₂) f₁
      comm _ := rfl
    }
    hom X := {
      h := Nat.le_min.2 (And.intro (X.π PullbackOb.A₁) (X.π PullbackOb.A₂))
      fac _ := rfl
    }
    unique _ _ := rfl
  }
