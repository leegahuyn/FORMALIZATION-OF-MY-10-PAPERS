import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleSheaf

/-!
# Restricting the support of the finite-support sheaf

The direct sum over a finite subset is a retract of the full direct sum.
The inclusion is extension by zero. Their composite is the identity on
sections whose support lies in the chosen subset.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

variable (S : Scheme.{u}) {I : Type}
  (P : I → Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0}) (t : Finset I)

private abbrev F := fun a ↦ (P a).obj

/-- The actual projection to the summands indexed by the chosen finite subset. -/
def finiteProjection : affineEtaleDirectSum S P ⟶
    affineEtaleDirectSum S (fun a : t ↦ P a.val) := by
  classical
  exact ⟨{
    app X := AddCommGrpCat.ofHom (DFinsupp.subtypeDomainAddMonoidHom
      (fun a ↦ ((F S P) a).obj X) (fun a ↦ a ∈ t))
    naturality {X Y} g := by
      apply ConcreteCategory.hom_ext
      intro x
      apply DFinsupp.ext
      intro a
      rfl }⟩

/-- Extension by zero from the chosen finite direct sum. -/
def finiteInclusion : affineEtaleDirectSum S (fun a : t ↦ P a.val) ⟶
    affineEtaleDirectSum S P := by
  classical
  exact ⟨{
    app X := AddCommGrpCat.ofHom ((DFinsupp.mkAddGroupHom t).comp DFinsupp.coeFnAddMonoidHom)
    naturality {X Y} g := by
      apply ConcreteCategory.hom_ext
      intro x
      apply DFinsupp.ext
      intro a
      change DFinsupp.mk t (fun b : t ↦ (F S P b.val).map g (x b)) a =
        (F S P a).map g (DFinsupp.mk t (fun b : t ↦ x b) a)
      by_cases ha : a ∈ t
      · rw [DFinsupp.mk_of_mem ha, DFinsupp.mk_of_mem ha]
      · rw [DFinsupp.mk_of_notMem ha, DFinsupp.mk_of_notMem ha]
        exact ((F S P a).map g).hom.map_zero.symm }⟩

/-- The coordinates of the projection are the corresponding original coordinates. -/
theorem finiteProjection_app (X : S.AffineEtaleᵒᵖ)
    (x : (affineEtaleDirectSum S P).obj.obj X) (a : t) :
    DFinsupp.toFun ((finiteProjection S P t).hom.app X x) a = DFinsupp.toFun x a.val := by
  classical
  rfl

/-- Extension by zero leaves the coordinates in the chosen subset unchanged. -/
theorem finiteInclusion_app_of_mem (X : S.AffineEtaleᵒᵖ)
    (x : (affineEtaleDirectSum S (fun a : t ↦ P a.val)).obj.obj X) {a : I} (ha : a ∈ t) :
    DFinsupp.toFun ((finiteInclusion S P t).hom.app X x) a = DFinsupp.toFun x ⟨a, ha⟩ := by
  classical
  exact DFinsupp.mk_of_mem ha

/-- Extension by zero vanishes on every component outside the chosen subset. -/
theorem finiteInclusion_app_of_notMem (X : S.AffineEtaleᵒᵖ)
    (x : (affineEtaleDirectSum S (fun a : t ↦ P a.val)).obj.obj X) {a : I} (ha : a ∉ t) :
    DFinsupp.toFun ((finiteInclusion S P t).hom.app X x) a = 0 := by
  classical
  exact DFinsupp.mk_of_notMem ha

/-- The projection retracts extension by zero. -/
theorem finiteInclusion_projection :
    finiteInclusion S P t ≫ finiteProjection S P t = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro x
  apply DFinsupp.ext
  intro a
  change DFinsupp.toFun ((finiteProjection S P t).hom.app X
    ((finiteInclusion S P t).hom.app X x)) a = DFinsupp.toFun x a
  rw [finiteProjection_app, finiteInclusion_app_of_mem S P t X x a.property]

/-- The finite-subset composite fixes every section supported on the chosen subset. -/
theorem projection_inclusion_of_support (X : S.AffineEtaleᵒᵖ)
    (x : (affineEtaleDirectSum S P).obj.obj X)
    (hx : ∀ a, a ∉ t → DFinsupp.toFun x a = 0) :
    (finiteInclusion S P t).hom.app X ((finiteProjection S P t).hom.app X x) = x := by
  apply DFinsupp.ext
  intro a
  change DFinsupp.toFun ((finiteInclusion S P t).hom.app X
    ((finiteProjection S P t).hom.app X x)) a = DFinsupp.toFun x a
  by_cases ha : a ∈ t
  · rw [finiteInclusion_app_of_mem S P t X _ ha, finiteProjection_app]
  · rw [finiteInclusion_app_of_notMem S P t X _ ha, hx a ha]

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteSupportPresheaf.finiteInclusion_projection,
      ``ManuscriptAudit.FiniteSupportPresheaf.projection_inclusion_of_support] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
