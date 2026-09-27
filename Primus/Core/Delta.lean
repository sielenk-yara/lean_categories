import Primus.Core.Category
import Primus.Core.Functor
import Primus.Core.NatTrans


def delta JJ {CC}(C: CC.Ob): Fun JJ CC := {
  onOb _ := C,
  onHom _ := CC.id C,
  id := Eq.refl (CC.id C),
  compose := Eq.symm (CC.left_id _)
}

def deltaFun JJ CC: Fun CC (functorCat JJ CC) := {
  onOb := delta JJ,
  onHom f := {
    η _ := f,
    naturality _ := Eq.trans (CC.right_id f) (Eq.symm (CC.left_id f))
  },
  id := Eq.refl _,
  compose := Eq.refl _
}

theorem deltaFun.faithful{JJ CC}[HJ: Nonempty JJ.Ob]:
   faithful (deltaFun JJ CC)
:= by
  intros A B f₁ f₂
  let ff₁ := (deltaFun JJ CC).onHom f₁
  let ff₂ := (deltaFun JJ CC).onHom f₂
  change ff₁ = ff₂ → _
  intro H
  apply HJ.elim
  intro J
  have H₁: f₁ = ff₁.η J := by rfl
  have H₂: f₂ = ff₂.η J := by rfl
  rw [H₁, H₂, H]
