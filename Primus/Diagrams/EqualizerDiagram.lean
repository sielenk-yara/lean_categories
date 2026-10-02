import Primus.Core.Category
import Primus.Core.Functor
import Primus.Limits.Lim
import Primus.Limits.CoLim


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
  preserves_id{X} := by
    cases X <;> rfl,
  preserves_compose{X Y Z g f} := by
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
         (X.comm equalizerDiagram.f₁)
         (Eq.symm (X.comm equalizerDiagram.f₂)))

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
          | EqualizerOb.B => by
              change f₁ ≪ eq ≪ h = _
              rw [←X.comm equalizerDiagram.f₁, ←Hh]
              change _ = f₁ ≪ (eq ≪ h)
              rw [CC.assoc]
      }

    unique X g := by
      let ⟨h, Hh⟩ := H2' X
      apply ConeHom.ext
      change g.h = h
      have Hg: eq ≪ g.h = X.π equalizerDiagram.A := g.fac equalizerDiagram.A
      rw [←Hg] at Hh
      apply Eq.symm
      apply H3 Hh
  }

abbrev Equalizer.E{CC: Cat.{m, n}}{A B: CC.Ob}
  {f₁: CC.Hom A B}{f₂: CC.Hom A B}
  (e: Equalizer f₁ f₂): CC.Ob
:=
  e.T.N

abbrev Equalizer.eq{CC: Cat.{m, n}}{A B: CC.Ob}
  {f₁: CC.Hom A B}{f₂: CC.Hom A B}
  (e: Equalizer f₁ f₂):
  CC.Hom e.E A
:=
  e.T.π equalizerDiagram.A

theorem Equalizer.eq_is_mono{CC: Cat}{A B: CC.Ob}{f₁ f₂: CC.Hom A B}(E: Equalizer f₁ f₂):
  mono E.eq
:= by
  intro O u₁ u₂ Hu
  let X: ConeOb (equalizerFunctor f₁ f₂) := {
    N := O
    π J := E.T.π J ≪ u₁
    comm f := by rw [CC.assoc, E.T.comm f]
  }
  let g₁: ConeHom X E.T := ⟨u₁, λ _ => rfl⟩
  let g₂: ConeHom X E.T := ⟨u₂, λ J => by
    cases J
    case A =>
      exact Hu.symm
    case B =>
      change E.T.π equalizerDiagram.B ≪ u₂ = E.T.π equalizerDiagram.B ≪ u₁
      rw [←E.T.comm EqualizerHom.f₁, ←CC.assoc, ←CC.assoc]
      change _ ≪ (E.eq ≪ u₂) = _ ≪ (E.eq ≪ u₁)
      rw [Hu]
    ⟩
  exact congrArg ConeHom.h (E.hom_ext g₁ g₂)


def CoEqualizer.{m, n}{CC: Cat.{m, n}}{A B: CC.Ob}
    (f₁: CC.Hom A B)(f₂: CC.Hom A B) : Sort _
:=
  CoLim (equalizerFunctor f₁ f₂)

def CoEqualizer.mk{CC: Cat}{A B}(f₁ f₂: CC.Hom A B)
  Q (q: CC.Hom B Q)
  (H1: q ≪ f₁ = q ≪ f₂)
  (H2: ∀{O}(m: CC.Hom B O), m ≪ f₁ = m ≪ f₂ -> { u // u ≪ q = m })
  (H3: epi q):
  CoEqualizer f₁ f₂
:= by
  let H2'(X: (coConeCat (equalizerFunctor f₁ f₂)).Ob) :=
    H2 (X.π EqualizerOb.B)
       (Eq.trans
         (X.comm equalizerDiagram.f₁)
         (Eq.symm (X.comm equalizerDiagram.f₂)))

  refine {
    I := {
      N := Q
      π J := match J with
        | EqualizerOb.A => q ≪ f₁
        | EqualizerOb.B => q
      comm f := match f with
        | EqualizerHom.idA => CC.right_id _
        | EqualizerHom.idB => CC.right_id _
        | EqualizerHom.f₁ => rfl
        | EqualizerHom.f₂ => Eq.symm H1
    }
    hom X := by
      let ⟨h, Hh⟩ := H2' X

      refine {
        h := h,
        fac J := match J with
          | EqualizerOb.A => by
              change h ≪ (q ≪ f₁) = _
              rw [←X.comm equalizerDiagram.f₁, ←Hh]
              change _ = h ≪ q ≪ f₁
              rw [CC.assoc]
          | EqualizerOb.B => Hh
      }

    unique X g := by
      let ⟨h, Hh⟩ := H2' X
      apply CoConeHom.ext
      change g.h = h
      have Hg: g.h ≪ q = X.π equalizerDiagram.B := g.fac equalizerDiagram.B
      rw [←Hg] at Hh
      apply Eq.symm
      apply H3 Hh
  }

abbrev CoEqualizer.Q{CC: Cat.{m, n}}{A B: CC.Ob}
  {f₁: CC.Hom A B}{f₂: CC.Hom A B}
  (e: CoEqualizer f₁ f₂): CC.Ob
:=
  e.I.N

abbrev CoEqualizer.q{CC: Cat.{m, n}}{A B: CC.Ob}
  {f₁: CC.Hom A B}{f₂: CC.Hom A B}
  (e: CoEqualizer f₁ f₂):
  CC.Hom B e.Q
:=
  e.I.π equalizerDiagram.B

theorem CoEqualizer.q_is_epi{CC: Cat}{A B: CC.Ob}{f₁ f₂: CC.Hom A B}(E: CoEqualizer f₁ f₂):
  epi E.q
:= by
  intro O u₁ u₂ Hu
  let X: CoConeOb (equalizerFunctor f₁ f₂) := {
    N := O
    π J := u₁ ≪ E.I.π J
    comm f := by rw [←CC.assoc, E.I.comm f]
  }
  let g₁: CoConeHom E.I X := ⟨u₁, λ _ => rfl⟩
  let g₂: CoConeHom E.I X := ⟨u₂, λ J => by
    cases J
    case A =>
      change u₂ ≪ E.I.π equalizerDiagram.A = u₁ ≪ E.I.π equalizerDiagram.A
      rw [←E.I.comm EqualizerHom.f₁, CC.assoc, CC.assoc]
      change _ ≪ E.q ≪ f₁ = _ ≪ E.q ≪ f₁
      rw [Hu]
    case B =>
      exact Hu.symm
    ⟩
  exact congrArg CoConeHom.h (E.hom_ext g₁ g₂)
