structure Cat.{m, n}: Sort _ where
  Ob: Sort m
  Hom: Ob -> Ob -> Sort n
  id(A:Ob): Hom A A
  compose{A B C: Ob}: Hom B C -> Hom A B -> Hom A C
  left_id {A B: Ob}(f: Hom A B): compose (id B) f = f
  right_id{A B: Ob}(f: Hom A B): compose f (id A) = f
  assoc{A B C D: Ob}(h: Hom C D)(g: Hom B C)(f: Hom A B):
         compose h (compose g f) = compose (compose h g) f

attribute [simp] Cat.left_id Cat.right_id

infixl:80 " ≪ " => Cat.compose _
infixl:80 " ≫ " => fun f g => g ≪ f

open Lean PrettyPrinter in
@[app_unexpander Cat.compose]
def unexpandCatCompose: Unexpander
  | `($_ $_ $g $f) => `($g ≪ $f)
  | _ => throw ()


structure InitialObject(CC: Cat): Sort _ where
  I: CC.Ob
  hom(X: CC.Ob): CC.Hom I X
  unique(X: CC.Ob): ∀g: CC.Hom I X, g = hom X

attribute [coe] InitialObject.I
instance{CC}: Coe (InitialObject CC) CC.Ob where coe i := i.I

theorem InitialObject.hom_ext{CC: Cat}(I: InitialObject CC){X: CC.Ob}
  (f₁ f₂: CC.Hom I X): f₁ = f₂
:=
  Eq.trans (I.unique X f₁) (Eq.symm (I.unique X f₂))

@[ext]
theorem InitialObject.ext{CC: Cat}{A B: InitialObject CC}:
  A.I = B.I -> A = B
:= by
  let ⟨I, ha, Ha⟩ := A
  let ⟨I', hb, Hb⟩ := B
  simp
  intro H
  subst H
  constructor
  . rfl
  . apply heq_of_eq
    funext X
    apply Hb


structure TerminalObject(CC: Cat): Sort _ where
  T: CC.Ob
  hom(X: CC.Ob): CC.Hom X T
  unique(X: CC.Ob): ∀g, g = hom X

attribute [coe] TerminalObject.T
instance{CC}: Coe (TerminalObject CC) CC.Ob where coe t := t.T

theorem TerminalObject.hom_ext{CC: Cat}(T: TerminalObject CC){X: CC.Ob}
  (f₁ f₂: CC.Hom X T): f₁ = f₂
:=
  Eq.trans (T.unique X f₁) (Eq.symm (T.unique X f₂))

@[ext]
theorem TerminalObject.ext{CC: Cat}{A B: TerminalObject CC}:
  A.T = B.T -> A = B
:= by
  let ⟨T, ha, Ha⟩ := A
  let ⟨T', hb, Hb⟩ := B
  simp
  intro H
  subst H
  constructor
  · rfl
  · apply heq_of_eq
    funext X
    apply Hb


@[reducible] def isomorphic{CC: Cat}(A B: CC.Ob): Prop :=
  ∃(f: CC.Hom A B)(g: CC.Hom B A), f ≫ g = CC.id A ∧ g ≫ f = CC.id B

@[reducible] def skeletal(CC: Cat): Prop :=
  ∀(A B: CC.Ob), isomorphic A B -> A = B

@[reducible] def thin(CC: Cat): Prop :=
  ∀(A B: CC.Ob)(f₁ f₂: CC.Hom A B), f₁ = f₂


section MorphismProperties
  variable {CC: Cat}
  variable {A B: CC.Ob}
  variable (f: CC.Hom A B)

  def mono: Prop :=
    ∀{X: CC.Ob}{g1 g2: CC.Hom X A}, f ≪ g1 = f ≪ g2 → g1 = g2

  def epi: Prop :=
    ∀{X: CC.Ob}{g1 g2: CC.Hom B X}, g1 ≪ f = g2 ≪ f → g1 = g2

  def splitMono: Prop :=
    ∃(g: CC.Hom B A), g ≪ f = CC.id A

  def splitEpi: Prop :=
    ∃(g: CC.Hom B A), f ≪ g = CC.id B

  def inverse(g: CC.Hom B A): Prop :=
    g ≪ f = CC.id A ∧ f ≪ g = CC.id B

  def iso: Prop :=
    ∃(g: CC.Hom B A), inverse f g

end MorphismProperties


theorem split_mono_to_mono{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitMono f → mono f
:= by
  intro ⟨g, H1⟩ X g1 g2 H2
  rw [←CC.left_id g1, ←CC.left_id g2, ←H1, ←CC.assoc, ←CC.assoc, H2]

theorem split_epi_to_epi{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitEpi f → epi f
:= by
  intro ⟨g, H1⟩ X g1 g2 H2
  rw [←CC.right_id g1, ←CC.right_id g2, ←H1, CC.assoc, CC.assoc, H2]

theorem split_mono_epi_to_iso{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitMono f -> epi f → iso f
:= by
  intro ⟨g, H1⟩ H2
  refine ⟨g, ⟨H1, H2 ?_⟩⟩
  rw [←CC.assoc, H1]
  simp

theorem split_epi_mono_to_iso{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitEpi f -> mono f → iso f
:= by
  intro ⟨g, H1⟩ H2
  refine ⟨g, ⟨H2 ?_, H1⟩⟩
  rw [CC.assoc, H1]
  simp

theorem iso_to_isomorphic{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  iso f -> isomorphic A B
:= by
  intro ⟨g, ⟨H1, H2⟩⟩
  exists f
  exists g

theorem id_is_iso{CC: Cat}(A: CC.Ob): iso (CC.id A) := by
  exists CC.id A
  and_intros
  apply CC.left_id
  apply CC.left_id
