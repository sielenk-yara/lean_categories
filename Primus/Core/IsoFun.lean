import Primus.Core.Category
import Primus.Core.Functor
import Primus.Core.NatTrans


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

attribute [coe] IsoFun
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


def equivalence_terminal {CC DD}:
    IsoFun CC DD -> TerminalObject CC -> TerminalObject DD
  := by
    intro ⟨F, G, H1, H2⟩ T

    let Ic := G.compose F
    let Id := F.compose G
    change Ic = _ at H1
    change Id = _ at H2

    have H3 (X: DD.Ob) : DD.Iso X (Id.onOb X) := by
      change DD.Iso X (Id.onOb X)
      rw [H2]
      exact id_as_iso X

    have H4 (X: CC.Ob) : CC.Iso X (Ic.onOb X) := by
      change CC.Iso X (Ic.onOb X)
      rw [H1]
      exact id_as_iso X

    refine ⟨F T.T, λ D => ?hom, λ D g => ?uniqe⟩
    case hom =>
      exact (F.onHom (T.hom (G D))) ≪ (H3 D).f
    case uniqe =>
      let C := T.T
      let i₁ : CC.Iso _ (Ic _):= (H4 C)
      let i₂ : DD.Iso _ (Id _) := (H3 D)
      change DD.Hom D (F C) at g

      rw [←T.unique (G D) ((H4 _).g ≪ (G.onHom g))]
      change _ = F.onHom (i₁.g ≪ G.onHom g) ≪ i₂.f

      have H5 := @F.preserves_compose _ _ _ i₁.g (G.onHom g)
      change _ = _ ≪ Id.onHom g at H5
      rw [H5]
      clear H5

      rw [Fun.congr_hom H2 _]
      simp only [Fun.id]
      rw [←DD.assoc]

      sorry
