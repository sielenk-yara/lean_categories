import Primus.Core.Category
import Primus.Core.Functor
import Primus.Limits.Lim


inductive EqualizerOb: Type
  | A: EqualizerOb
  | B: EqualizerOb
deriving DecidableEq, Inhabited

inductive EqualizerHom: EqualizerOb -> EqualizerOb -> Type
  | idA: EqualizerHom EqualizerOb.A EqualizerOb.A
  | idB: EqualizerHom EqualizerOb.B EqualizerOb.B
  | f₁: EqualizerHom EqualizerOb.A EqualizerOb.B
  | f₂: EqualizerHom EqualizerOb.A EqualizerOb.B
deriving DecidableEq

def equalizerDiagram: Cat.{1, 1} := {
  Ob := EqualizerOb
  Hom := EqualizerHom
  id X := match X with
    | EqualizerOb.A => EqualizerHom.idA
    | EqualizerOb.B => EqualizerHom.idB
  compose g f := match f, g with
    | EqualizerHom.idA, EqualizerHom.idA => EqualizerHom.idA
    | EqualizerHom.idB, EqualizerHom.idB => EqualizerHom.idB
    | EqualizerHom.f₁, EqualizerHom.idB => EqualizerHom.f₁
    | EqualizerHom.f₂, EqualizerHom.idB => EqualizerHom.f₂
    | EqualizerHom.idA, EqualizerHom.f₁ => EqualizerHom.f₁
    | EqualizerHom.idA, EqualizerHom.f₂ => EqualizerHom.f₂
  left_id f := by
    cases f <;> rfl
  right_id f:= by
    cases f <;> rfl
  assoc h g f := by
    cases h <;> cases g <;> cases f <;> rfl
}

abbrev equalizerDiagram.A: equalizerDiagram.Ob := EqualizerOb.A
abbrev equalizerDiagram.B: equalizerDiagram.Ob := EqualizerOb.B
abbrev equalizerDiagram.f₁: equalizerDiagram.Hom A B := EqualizerHom.f₁
abbrev equalizerDiagram.f₂: equalizerDiagram.Hom A B  := EqualizerHom.f₂

@[simp] theorem equalizerDiaOb: EqualizerOb = equalizerDiagram.Ob := rfl
@[simp] theorem equalizerDiaHom: EqualizerHom = equalizerDiagram.Hom := rfl
@[simp] theorem equalizerIdA: EqualizerHom.idA = equalizerDiagram.id equalizerDiagram.A := rfl
@[simp] theorem equalizerIdB: EqualizerHom.idB = equalizerDiagram.id equalizerDiagram.B := rfl

def equalizerFunctor.{m, n}{CC: Cat.{m, n}}{A B: CC.Ob}
    (f₁ f₂: CC.Hom A B): Fun.{1, 1, m, n} equalizerDiagram CC
:= {
  onOb X := match X with
    | EqualizerOb.A => A
    | EqualizerOb.B => B,
  onHom f := match f with
    | EqualizerHom.idA => CC.id A
    | EqualizerHom.idB => CC.id B
    | EqualizerHom.f₁ => f₁
    | EqualizerHom.f₂ => f₂
  id{X} := by
    cases X <;> rfl,
  compose{X Y Z g f} := by
    cases g <;> cases f <;> simp <;> rfl
}

@[simp] theorem equalizerF₁{CC: Cat}{A B: CC.Ob}(f₁ f₂: CC.Hom A B):
    (equalizerFunctor f₁ f₂).onHom (equalizerDiagram.f₁) = f₁
:=
  rfl

@[simp] theorem equalizerF₂{CC: Cat}{A B: CC.Ob}(f₁ f₂: CC.Hom A B):
    (equalizerFunctor f₁ f₂).onHom (equalizerDiagram.f₂) = f₂
:=
  rfl

def Equalizer.{m, n}{CC: Cat.{m, n}}{A B: CC.Ob}
    (f₁: CC.Hom A B)(f₂: CC.Hom A B) : Sort _
:=
  Lim (equalizerFunctor f₁ f₂)

def Equalizer.mk{CC: Cat}{A B}(f₁ f₂: CC.Hom A B)
  E (eq: CC.Hom E A)
  (H1: f₁ ≪ eq = f₂ ≪ eq)
  (H2: ∀{O}(m: CC.Hom O A), f₁ ≪ m = f₂ ≪ m -> { u // eq ≪ u = m })
  (H3: mono eq):
  Equalizer f₁ f₂
:= by
  let H2'(X: (coneCat (equalizerFunctor f₁ f₂)).Ob) :=
    H2 (X.π EqualizerOb.A)
       (Eq.trans
         (X.comm EqualizerHom.f₁)
         (Eq.symm (X.comm EqualizerHom.f₂)))

  refine {
    T := {
      N := E
      π J := match J with
        | EqualizerOb.A => eq
        | EqualizerOb.B => f₁ ≪ eq
      comm f := match f with
        | EqualizerHom.idA => CC.left_id _
        | EqualizerHom.idB => CC.left_id _
        | EqualizerHom.f₁ => rfl
        | EqualizerHom.f₂ => Eq.symm H1
    }
    hom X := by
      let ⟨h, Hh⟩ := H2' X
      refine {
        h := h,
        fac J := match J with
          | EqualizerOb.A => Hh
          | EqualizerOb.B => ?_
      }
      simp
      rw [←X.comm EqualizerHom.f₁, ←Hh]
      apply Eq.symm
      apply CC.assoc

    unique X g := by
      let ⟨h, Hh⟩ := H2' X
      apply ConeHom.ext
      simp
      have Hg: eq ≪ g.h = X.π EqualizerOb.A := g.fac EqualizerOb.A
      rw [←Hg] at Hh
      apply Eq.symm
      apply H3 Hh
  }
