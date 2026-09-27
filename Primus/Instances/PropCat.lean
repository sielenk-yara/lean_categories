import Primus.Core.Category
import Primus.Core.Functor
import Primus.Diagrams.Discrete
import Primus.Diagrams.Two
import Primus.Limits.CoLim
import Primus.Diagrams.EqualizerDiagram


def propCat: Cat.{1, 0} := {
  Ob := Prop,
  Hom A B :=  A -> B,
  id _ x := x,
  compose g f x := g (f x)
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def propCat.initial: InitialObject propCat := {
  I := False
  hom X := False.elim
  unique X g := by
    funext x
    exact x.elim
}

def propCat.terminal: TerminalObject propCat := {
  T := True
  hom _ _ := True.intro
  unique _ _ := rfl
}

theorem propCat.is_mono{A B: propCat.Ob}(f: propCat.Hom A B): mono f :=
  λ _ ↦ rfl

theorem propCat.is_epi{A B: propCat.Ob}(f: propCat.Hom A B): epi f :=
  λ _ ↦ rfl

theorem propCat.is_thin: thin propCat :=
  λ _ _ _ _ ↦ rfl

def propCat.lim{JJ: Cat}(F: Fun JJ propCat): Lim F := {
  T := {
    N := ∀J, F J
    π J H := H J
    comm _ := rfl
  }
  hom X := {
    h n J := X.π J n
    fac _ := rfl
  }
  unique _ _ := rfl
}

def propCat.coLim{JJ: Cat}(F: Fun JJ propCat): CoLim F := {
  I := {
    N := ∃J, F J
    π J H := ⟨J, H⟩
    comm _ := rfl
  }
  hom X := {
    h := λ⟨J, n⟩ ↦ X.π J n
    fac _ := rfl
  }
  unique _ _ := rfl
}
