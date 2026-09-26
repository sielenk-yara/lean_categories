import Primus.Core.Category


inductive ThreeOb.{m}: Type m
  | ob1: ThreeOb
  | ob2: ThreeOb
  | ob3: ThreeOb
deriving DecidableEq, Inhabited

inductive ThreeHom.{m, n}: ThreeOb.{m} -> ThreeOb.{m} -> Type n
  | id1: ThreeHom ThreeOb.ob1 ThreeOb.ob1
  | id2: ThreeHom ThreeOb.ob2 ThreeOb.ob2
  | id3: ThreeHom ThreeOb.ob3 ThreeOb.ob3
  | f12: ThreeHom ThreeOb.ob1 ThreeOb.ob2
  | f23: ThreeHom ThreeOb.ob2 ThreeOb.ob3
  | f13: ThreeHom ThreeOb.ob1 ThreeOb.ob3
deriving DecidableEq

def threeId(A: ThreeOb): ThreeHom A A :=
  match A with
  | ThreeOb.ob1 => ThreeHom.id1
  | ThreeOb.ob2 => ThreeHom.id2
  | ThreeOb.ob3 => ThreeHom.id3

def threeComp{A B C: ThreeOb}(g: ThreeHom B C)(f: ThreeHom A B): ThreeHom A C :=
  match f, g with
  | ThreeHom.id1, ThreeHom.id1 => ThreeHom.id1
  | ThreeHom.id1, ThreeHom.f12 => ThreeHom.f12
  | ThreeHom.id1, ThreeHom.f13 => ThreeHom.f13
  | ThreeHom.id2, ThreeHom.id2 => ThreeHom.id2
  | ThreeHom.id2, ThreeHom.f23 => ThreeHom.f23
  | ThreeHom.id3, ThreeHom.id3 => ThreeHom.id3
  | ThreeHom.f12, ThreeHom.id2 => ThreeHom.f12
  | ThreeHom.f12, ThreeHom.f23 => ThreeHom.f13
  | ThreeHom.f13, ThreeHom.id3 => ThreeHom.f13
  | ThreeHom.f23, ThreeHom.id3 => ThreeHom.f23

@[simp] theorem threeId1: ThreeHom.id1 = threeId ThreeOb.ob1 := rfl
@[simp] theorem threeId2: ThreeHom.id2 = threeId ThreeOb.ob2 := rfl
@[simp] theorem threeId3: ThreeHom.id3 = threeId ThreeOb.ob3 := rfl

@[simp] theorem threeLeftId {A B: ThreeOb}(f: ThreeHom A B): threeComp (threeId B) f = f := by
  cases f <;> rfl

@[simp] theorem threeRightId {A B: ThreeOb}(f: ThreeHom A B): threeComp f (threeId A) = f := by
  cases f <;> rfl

def three.{m, n}: Cat.{m+1, n+1} := {
  Ob := ThreeOb.{m},
  Hom := ThreeHom.{m, n},
  id := threeId,
  compose := threeComp,
  left_id := threeLeftId,
  right_id := threeRightId,
  assoc h g f := by
    cases g <;> try simp
    · case f12 =>
      cases f ; simp
    · case f23 =>
      cases h ; simp
    · case f13 =>
      cases f ; cases h ; simp
}
