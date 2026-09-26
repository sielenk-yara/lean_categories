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

def equalizerDiagram: Cat := {
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

@[simp] theorem equalizerIdA: EqualizerHom.idA = equalizerDiagram.id EqualizerOb.A := rfl
@[simp] theorem equalizerIdB: EqualizerHom.idB = equalizerDiagram.id EqualizerOb.B := rfl

def equalizerFunctor.{m, n}{CC: Cat.{m, n}}{A B: CC.Ob}
    (f₁ f₂: CC.Hom A B): Fun.{1, 1, m, n} equalizerDiagram CC := {
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
    (equalizerFunctor f₁ f₂).onHom (EqualizerHom.f₁) = f₁ := rfl
@[simp] theorem equalizerF₂{CC: Cat}{A B: CC.Ob}(f₁ f₂: CC.Hom A B):
    (equalizerFunctor f₁ f₂).onHom (EqualizerHom.f₂) = f₂ := rfl

def Equalizer.{m, n}{CC: Cat.{m, n}}{A B: CC.Ob}
    (f₁: CC.Hom A B)(f₂: CC.Hom A B) : Sort _ :=
  Lim (equalizerFunctor f₁ f₂)
