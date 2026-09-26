import Primus.Core.Category


inductive FourOb.{m}: Type m
  | ob1: FourOb
  | ob2: FourOb
  | ob3: FourOb
  | ob4: FourOb
deriving DecidableEq, Inhabited

inductive FourHom.{m, n}: FourOb.{m} -> FourOb.{m} -> Type n
  | id1: FourHom FourOb.ob1 FourOb.ob1
  | f12: FourHom FourOb.ob1 FourOb.ob2
  | f13: FourHom FourOb.ob1 FourOb.ob3
  | f14: FourHom FourOb.ob1 FourOb.ob4
  | id2: FourHom FourOb.ob2 FourOb.ob2
  | f23: FourHom FourOb.ob2 FourOb.ob3
  | f24: FourHom FourOb.ob2 FourOb.ob4
  | id3: FourHom FourOb.ob3 FourOb.ob3
  | f34: FourHom FourOb.ob3 FourOb.ob4
  | id4: FourHom FourOb.ob4 FourOb.ob4
deriving DecidableEq

def fourId(A: FourOb): FourHom A A :=
  match A with
  | FourOb.ob1 => FourHom.id1
  | FourOb.ob2 => FourHom.id2
  | FourOb.ob3 => FourHom.id3
  | FourOb.ob4 => FourHom.id4

def fourComp{A B C: FourOb}(g: FourHom B C)(f: FourHom A B): FourHom A C :=
  match f, g with
  | FourHom.id1, FourHom.id1 => FourHom.id1
  | FourHom.id1, FourHom.f12 => FourHom.f12
  | FourHom.id1, FourHom.f13 => FourHom.f13
  | FourHom.id1, FourHom.f14 => FourHom.f14
  | FourHom.id2, FourHom.id2 => FourHom.id2
  | FourHom.id2, FourHom.f23 => FourHom.f23
  | FourHom.id2, FourHom.f24 => FourHom.f24
  | FourHom.id3, FourHom.id3 => FourHom.id3
  | FourHom.id3, FourHom.f34 => FourHom.f34
  | FourHom.id4, FourHom.id4 => FourHom.id4
  | FourHom.f12, FourHom.id2 => FourHom.f12
  | FourHom.f12, FourHom.f23 => FourHom.f13
  | FourHom.f12, FourHom.f24 => FourHom.f14
  | FourHom.f13, FourHom.id3 => FourHom.f13
  | FourHom.f13, FourHom.f34 => FourHom.f14
  | FourHom.f14, FourHom.id4 => FourHom.f14
  | FourHom.f23, FourHom.id3 => FourHom.f23
  | FourHom.f23, FourHom.f34 => FourHom.f24
  | FourHom.f24, FourHom.id4 => FourHom.f24
  | FourHom.f34, FourHom.id4 => FourHom.f34

def four.{m, n}: Cat.{m+1, n+1} := {
  Ob := FourOb.{m}
  Hom := FourHom.{m, n}
  id := fourId
  compose := fourComp
  left_id f := by
    cases f <;> rfl
  right_id f := by
    cases f <;> rfl
  assoc h g f := by
    cases h <;> cases g <;> cases f <;> rfl
}
