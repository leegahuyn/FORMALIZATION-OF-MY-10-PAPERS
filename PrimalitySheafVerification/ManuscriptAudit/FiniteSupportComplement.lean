import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleRetraction
import PrimalitySheafVerification.ManuscriptAudit.SheafHOnePushout

/-! Complementary projections of actual finite-support étale sheaves. -/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (S : Scheme.{0}) {I : Type}
variable (P : I → Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0})
variable (t : Finset I)

private abbrev D := affineEtaleDirectSum S P

/-- The endomorphism that discards the components in the finite subset. -/
def finiteComplement : D S P ⟶ D S P :=
  𝟙 _ - (finiteProjection S P t ≫ finiteInclusion S P t)

theorem finiteComplement_app_eq_zero_of_support (W : S.AffineEtaleᵒᵖ)
    (x : (D S P).obj.obj W) (hx : ∀ a, a ∉ t → DFinsupp.toFun x a = 0) :
    (finiteComplement S P t).hom.app W x = 0 := by
  change x - (finiteInclusion S P t).hom.app W
    ((finiteProjection S P t).hom.app W x) = 0
  rw [projection_inclusion_of_support S P t W x hx, sub_self]

variable {M : Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0}} (i : D S P ⟶ M)

/-- Pushing out along the complementary projection kills the images
of sections supported on the discarded coordinates. -/
theorem pushout_inl_app_eq_zero_of_support (W : S.AffineEtaleᵒᵖ)
    (x : (D S P).obj.obj W) (hx : ∀ a, a ∉ t → DFinsupp.toFun x a = 0) :
    (pushout.inl i (finiteComplement S P t)).hom.app W (i.hom.app W x) = 0 := by
  let ρ := finiteComplement S P t
  let T := pushout i ρ
  have hc := congrArg (fun e : D S P ⟶ T ↦ e.hom.app W) (pushout.condition (f := i) (g := ρ))
  rw [show (pushout.inl i ρ).hom.app W (i.hom.app W x) =
    (pushout.inr i ρ).hom.app W (ρ.hom.app W x) from ConcreteCategory.congr_hom hc x]
  rw [finiteComplement_app_eq_zero_of_support S P t W x hx]
  exact ((pushout.inr i ρ).hom.app W).hom.map_zero

variable [HasExt.{0} (Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0})]

/-- If the discarded finite sum has vanishing degree-n cohomology,
the complementary projection acts as the identity in that degree. -/
theorem H_map_finiteComplement_eq_self (n : ℕ)
    (h : Subsingleton (Sheaf.H (affineEtaleDirectSum S (fun a : t ↦ P a.val)) n))
    (x : Sheaf.H (D S P) n) :
    Sheaf.H.map (finiteComplement S P t) n x = x := by
  let H := Sheaf.functorH (Scheme.AffineEtale.topology S) n
  let p := finiteProjection S P t
  let k := finiteInclusion S P t
  have hP : Sheaf.H.map p n x = 0 := h.elim _ _
  have hMap : H.map (finiteComplement S P t) = 𝟙 (H.obj (D S P)) - (H.map p ≫ H.map k) := by
    change H.map (𝟙 (D S P) - (p ≫ k)) = _
    rw [H.map_sub, H.map_id, H.map_comp]
  have hApply := ConcreteCategory.congr_hom hMap x
  change Sheaf.H.map (finiteComplement S P t) n x =
    x - Sheaf.H.map k n (Sheaf.H.map p n x) at hApply
  rwa [hP, map_zero, sub_zero] at hApply

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteSupportPresheaf.pushout_inl_app_eq_zero_of_support,
      ``ManuscriptAudit.FiniteSupportPresheaf.H_map_finiteComplement_eq_self] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
