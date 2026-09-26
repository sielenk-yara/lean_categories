import Primus.Core.Category
import Primus.Core.Functor
import Primus.Limits.Lim


inductive PullbackOb: Type
  | A₁: PullbackOb
  | A₂: PullbackOb
  | B: PullbackOb
deriving DecidableEq, Inhabited

inductive PullbackHom: PullbackOb -> PullbackOb -> Type
  | idA₁: PullbackHom PullbackOb.A₁ PullbackOb.A₁
  | idA₂: PullbackHom PullbackOb.A₂ PullbackOb.A₂
  | idB: PullbackHom PullbackOb.B PullbackOb.B
  | f₁: PullbackHom PullbackOb.A₁ PullbackOb.B
  | f₂: PullbackHom PullbackOb.A₂ PullbackOb.B
deriving DecidableEq

def pullbackId(A: PullbackOb): PullbackHom A A :=
  match A with
  | PullbackOb.A₁ => PullbackHom.idA₁
  | PullbackOb.A₂ => PullbackHom.idA₂
  | PullbackOb.B => PullbackHom.idB

def pullbackComp{X Y Z: PullbackOb}(g: PullbackHom Y Z)(f: PullbackHom X Y): PullbackHom X Z :=
  match f, g with
  | PullbackHom.idA₁, PullbackHom.idA₁ => PullbackHom.idA₁
  | PullbackHom.idA₁, PullbackHom.f₁ => PullbackHom.f₁
  | PullbackHom.idA₂, PullbackHom.f₂ => PullbackHom.f₂
  | PullbackHom.idA₂, PullbackHom.idA₂ => PullbackHom.idA₂
  | PullbackHom.f₁, PullbackHom.idB => PullbackHom.f₁
  | PullbackHom.f₂, PullbackHom.idB => PullbackHom.f₂
  | PullbackHom.idB, PullbackHom.idB => PullbackHom.idB

@[simp] theorem pullbackIdA₁: PullbackHom.idA₁ = pullbackId PullbackOb.A₁ := rfl
@[simp] theorem pullbackIdA₂: PullbackHom.idA₂ = pullbackId PullbackOb.A₂ := rfl
@[simp] theorem pullbackIdB: PullbackHom.idB = pullbackId PullbackOb.B := rfl

@[simp] theorem pullbackLeftId {X Y: PullbackOb}(f: PullbackHom X Y): pullbackComp (pullbackId Y) f = f := by
  cases f <;> rfl

@[simp] theorem pullbackRightId {X Y: PullbackOb}(f: PullbackHom X Y): pullbackComp f (pullbackId X) = f := by
  cases f <;> rfl

def pullbackDiagram: Cat.{1, 1} := {
  Ob := PullbackOb,
  Hom := PullbackHom,
  id := pullbackId,
  compose := pullbackComp,
  left_id := pullbackLeftId,
  right_id := pullbackRightId,
  assoc h g f := by
    cases g <;> cases f <;> simp
}


def pullbackFunctor{CC: Cat}{A₁ A₂ B: CC.Ob}
    (f₁: CC.Hom A₁ B)(f₂: CC.Hom A₂ B): Fun pullbackDiagram CC := {
  onOb A := match A with
    | PullbackOb.A₁ => A₁
    | PullbackOb.A₂ => A₂
    | PullbackOb.B => B,
  onHom f := match f with
    | PullbackHom.idA₁ => CC.id A₁
    | PullbackHom.idA₂ => CC.id A₂
    | PullbackHom.idB => CC.id B
    | PullbackHom.f₁ => f₁
    | PullbackHom.f₂ => f₂
  id{X} := by
    cases X <;> rfl,
  compose{X Y Z g f} := by
    cases g <;> cases f <;> simp <;> rfl
}

def Pullback{CC: Cat}{A₁ A₂ B: CC.Ob}
    (f₁: CC.Hom A₁ B)(f₂: CC.Hom A₂ B) :=
  Lim (pullbackFunctor f₁ f₂)
