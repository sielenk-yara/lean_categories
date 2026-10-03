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

def foo{CC DD}(I: IsoFun CC DD): NaturalTransformation (I.F.compose I.G) (Fun.id DD):= {
  η X : DD.Hom (I.F (I.G X)) X := by
    change DD.Hom ((I.F.compose I.G) X) X
    rw [I.FG_is_id]
    apply DD.id
  naturality := by
    intros A B f
    change _ ≪ _ = f ≪ _
    rw [I.FG_is_id]
}


def equivalence_terminal {CC DD}:
    IsoFun CC DD -> TerminalObject CC -> TerminalObject DD
  := by
    intro ⟨F, G, H1, H2⟩ T

    let H3 (X: DD.Ob) : DD.Iso X (F.onOb (G.onOb X)) := by
      change DD.Iso X ((F.compose G).onOb X)
      rw [H2]
      exact id_as_iso X

    let H4 (X: CC.Ob) : CC.Iso X (G.onOb (F.onOb X)) := by
      change CC.Iso X ((G.compose F).onOb X)
      rw [H1]
      exact id_as_iso X

    refine ⟨F T.T, λ X => ?hom, λ X g => ?uniqe⟩
    case hom =>
      exact (F.onHom (T.hom (G X))) ≪ (H3 X).f
    case uniqe =>
      let Ic := G.compose F
      let Id := F.compose G
      let i₁ : CC.Iso _ (Ic _):= (H4 T.T)
      let i₂ : DD.Iso _ (Id _) := (H3 X)

      rw [←T.unique (G X) ((H4 _).g ≪ (G.onHom g))]
      simp only [F.preserves_compose]
      change _ = F.onHom i₁.g ≪ Id.onHom g ≪ i₂.f

      rw [H1] at Ic
