import Primus.Core.Category
import Primus.Core.Functor
import Primus.Core.NatTrans
import Primus.Core.Opposite


structure IsoFun(CC DD: Cat): Sort _ where
  F : Fun CC DD
  G : Fun DD CC
  GF_is_id : Fun.compose G F = Fun.id CC
  FG_is_id : Fun.compose F G = Fun.id DD

def IsoFun.inverse{CC DD: Cat}:
  IsoFun CC DD -> IsoFun DD CC
:= by
  intro ⟨F, G, H1, H2⟩
  exact ⟨G, F, H2, H1⟩

def IsoFun.ofIso{CC DD}: categoryCat.Iso CC DD -> IsoFun CC DD := by
  intro ⟨F, G, H1, H2⟩
  exact ⟨F, G, H1, H2⟩

def IsoFun.toIso{CC DD}: IsoFun CC DD -> categoryCat.Iso CC DD := by
  intro ⟨F, G, H1, H2⟩
  exact ⟨F, G, H1, H2⟩


def IsoFun.refl(CC: Cat): IsoFun CC CC :=
  ⟨Fun.id CC, Fun.id CC, rfl, rfl⟩

abbrev IsoFun.symm{CC DD: Cat} :=
  @IsoFun.inverse CC DD

def IsoFun.trans{AA BB CC: Cat}(F: IsoFun AA BB)(G: IsoFun BB CC): IsoFun AA CC :=
  IsoFun.ofIso (F.toIso.trans G.toIso)

instance: Trans IsoFun IsoFun IsoFun where trans := IsoFun.trans


attribute [coe] IsoFun.F
instance{CC DD}: Coe (IsoFun CC DD) (Fun CC DD) where
  coe I := I.F

@[ext]
theorem IsoFun.ext{CC DD: Cat}{I₁ I₂: IsoFun CC DD}:
  I₁.F = I₂.F -> I₁ = I₂
:= by
  let ⟨F₁, G₁, HFG₁, HGF₁⟩ := I₁
  let ⟨F₂, G₂, HFG₂, HGF₂⟩ := I₂
  simp only [mk.injEq]
  intro H1
  and_intros
  . assumption
  . rw [←Fun.left_id G₁, ←HFG₂, ←H1, ←Fun.assoc, HGF₁, Fun.right_id]

theorem Fun.onIso_eq_as_iso{CC DD: Cat}(F: Fun CC DD){A B: CC.Ob}(H: A = B):
  F.onIso (eq_as_iso H) = eq_as_iso (congrArg F.onOb H)
:= by
  cases H
  ext
  exact F.preserves_id

@[simp]
theorem Fun.onIso_f{CC DD: Cat}(F: Fun CC DD){A B: CC.Ob}(i: CC.Iso A B):
  (F.onIso i).f = F.onHom i.f
:= by
  cases i
  rfl

def Cat.opOpIso(CC: Cat): IsoFun (op (op CC)) CC :=
  IsoFun.refl CC

def Cat.core.opIso(CC: Cat): IsoFun (op CC.core) CC.core :=
  ⟨
    {
      onOb A := A
      onHom f := f.inverse
      preserves_id := rfl
      preserves_compose := rfl
    },
    {
      onOb A := A
      onHom f := f.inverse
      preserves_id := rfl
      preserves_compose := rfl
    },
    rfl,
    rfl
  ⟩


def equivalence_terminal {CC DD}:
    IsoFun CC DD -> TerminalObject CC -> TerminalObject DD
  := by
    intro ⟨F, G, H1, H2⟩ T

    let nt₁ := NaturalIso.ofEq H1
    let nt₂ := NaturalIso.ofEq H2

    have H3 A: (nt₂.η (F.onOb A)) = F.onIso (nt₁.η A) := by
      show (NaturalIso.ofEq H2).η _ = F.onIso ((NaturalIso.ofEq H1).η A)
      rw [NaturalIso.ofEq_eta, NaturalIso.ofEq_eta, Fun.onIso_eq_as_iso]
      rfl

    refine ⟨
        F T.T,
        λ D => (F.onHom (T.u (G D))) ≪ (nt₂.η D).g,
        λ D g => ?uniqe
      ⟩
    case uniqe =>
      rw [←T.unique (G D) ((nt₁.η T).f ≪ (G.onHom g))]
      have H: @F.onHom _ T ((nt₁.η T).f ≪ G.onHom g) = _ := F.preserves_compose
      rw [H]
      clear H
      show g = F.onHom (nt₁.η T).f ≪ _ ≪ (nt₂.η D).g
      have H := @DD.assoc _ _ _ _ (F.onHom (nt₁.η T).f) (F.onHom (G.onHom g)) (nt₂.η D).g
      show _ = (F.onHom (nt₁.η T).f) ≪ (F.onHom (G.onHom g)) ≪ (nt₂.η D).g
      rw [←H]
      clear H
      let x := (F.onHom (G.onHom g)) ≪ (nt₂.η D).g
      have H: (nt₂.η (F.onOb T)).g ≪ g = x := nt₂.inverse.naturality g
      show g = F.onHom (nt₁.η T).f ≪ x
      rw [←H]
      clear H x
      have H := DD.assoc (F.onHom (nt₁.η T).f) ((nt₂.η (F.onOb T)).g) g
      show g = F.onHom (nt₁.η T).f ≪ ((nt₂.η (F.onOb T)).g ≪ g)
      rw [H]
      clear H
      apply Eq.trans (b := DD.id _ ≪ g)
      · simp
      · congr
        clear g D
        apply Eq.trans
        apply ((nt₂.η (F.onOb ↑T)).fg_is_id).symm
        congr
        rw [H3]
        rfl
