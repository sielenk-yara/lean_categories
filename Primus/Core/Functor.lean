import Primus.Core.Category
import Primus.Diagrams.Zero
import Primus.Diagrams.One


structure Fun(CC DD: Cat): Sort _ where
  onOb: CC.Ob -> DD.Ob
  onHom{A B: CC.Ob}: CC.Hom A B -> DD.Hom (onOb A) (onOb B)
  preserves_id{A: CC.Ob}: onHom (CC.id A) = DD.id (onOb A)
  preserves_compose{A B C: CC.Ob}{g: CC.Hom B C}{f: CC.Hom A B}:
         onHom (g ≪ f) = onHom g ≪ onHom f

attribute [simp] Fun.preserves_id
attribute [simp] Fun.preserves_compose

instance {CC DD: Cat}: CoeFun (Fun CC DD) (λ _ => CC.Ob → DD.Ob) where
  coe F := F.onOb

@[ext]
theorem Fun.ext{CC DD: Cat}{F G: Fun CC DD}
    (h_ob : ∀ A, F A = G A)
    (h_hom : ∀{A B}(f : CC.Hom A B), F.onHom f ≍ G.onHom f):
    F = G
:= by
  cases F with | mk Fob Fhom Fid Fcomp =>
  cases G with | mk Gob Ghom Gid Gcomp =>
  have hob : Fob = Gob := funext h_ob
  subst hob
  simp
  funext A B f
  apply eq_of_heq (h_hom f)


section FunctorProperties
  variable {CC DD: Cat}
  variable (F: Fun CC DD)

  def faithful: Prop :=
    ∀{A B: CC.Ob}, Function.Injective (@F.onHom A B)

  def full: Prop :=
    ∀{A B: CC.Ob}, Function.Surjective (@F.onHom A B)

  def fullyFaithful: Prop :=
    full F ∧ faithful F

  def essentiallySurjective: Prop :=
    ∀(D: DD.Ob), ∃(C: CC.Ob), isomorphic (F C) D

  def equivalence: Prop :=
    fullyFaithful F ∧ essentiallySurjective F

end FunctorProperties


def Fun.id.{m, n}(AA: Cat.{m, n}): Fun.{m, n, m, n} AA AA := {
    onOb A := A
    onHom f:= f
    preserves_id{A} := by simp only
    preserves_compose := by simp only [implies_true]
}

def Fun.compose{AA BB CC: Cat}(G: Fun BB CC)(F: Fun AA BB): Fun AA CC := {
    onOb A := G (F A),
    onHom f := G.onHom (F.onHom f),
    preserves_id := by simp,
    preserves_compose := by simp
}

theorem Fun.left_id{CC DD: Cat}(F: Fun CC DD):
  compose (id DD) F = F
:= by
  apply Fun.ext
  intro A
  rfl
  intros A B f
  apply heq_of_eq
  rfl

theorem Fun.right_id{CC DD: Cat}(F: Fun CC DD):
  compose F (id CC) = F
:= by
  apply Fun.ext
  intro A
  rfl
  intros A B f
  apply heq_of_eq
  rfl

theorem Fun.assoc{AA BB CC DD: Cat}(H: Fun CC DD)(G: Fun BB CC)(F: Fun AA BB):
         compose H (compose G F) = compose (compose H G) F
:= by
  apply Fun.ext
  intro A
  rfl
  intros A B f
  apply heq_of_eq
  rfl


/-- The `checkUnivs` warning on this declaration is a false positive, so do not
    "fix" it by collapsing `m` and `n` into one level. The linter only inspects
    the *type*, where the two occur solely as `max m n`; the body uses them
    separately in `Ob := Cat.{m, n}`, so `CategoryCat.{0, 1}` and
    `CategoryCat.{1, 0}` have genuinely different objects. -/
def categoryCat.{m, n} : Cat.{(max m n) + 1, max 1 (max m n)} := {
  Ob := Cat.{m, n}
  Hom := Fun.{m, n, m, n}
  id := Fun.id,
  compose := Fun.compose,
  left_id := Fun.left_id,
  right_id := Fun.right_id,
  assoc := Fun.assoc
}

def categoryCat.terminal: TerminalObject categoryCat := {
  T := one
  hom X := {
    onOb A := PUnit.unit
    onHom f := PUnit.unit
    preserves_id := rfl
    preserves_compose := rfl
  }
  unique {CC} F := by
    congr
}

theorem faithful_comp{AA BB CC}(G: Fun BB CC)(F: Fun AA BB):
  faithful F -> faithful G → faithful (categoryCat.compose G F)
:= by
  intro H1 H2 A B f1 f2 H3
  apply H1
  apply H2
  assumption

theorem full_comp{AA BB CC}(G: Fun BB CC)(F: Fun AA BB):
  full F -> full G → full (categoryCat.compose G F)
:= by
  intro H1 H2 A B g
  let ⟨a, H3⟩ := (H2 g)
  let ⟨b, H4⟩ := (H1 a)
  exists b
  rw [←H3, ←H4]
  simp only [categoryCat, Fun.compose]


def equivalent(CC DD: Cat): Prop :=
  ∃(F: Fun CC DD), equivalence F
