import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleLocallyConstantHausdorff
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleResidueComparison

/-! On a locally Noetherian scheme, restricting a pro-étale continuous
Hausdorff-valued coefficient sheaf to the small étale site gives the
constant sheaf of the underlying discrete coefficient group. -/

namespace ManuscriptAudit.EtaleProetaleHausdorffDirectImage

open AlgebraicGeometry CategoryTheory Opposite
open EtaleProetaleResidueComparison (directImage)
open EtaleContinuousMapSheaf (continuousMapSheaf constantSheafContinuousMapIso)
open ProetaleResidueSheaves (continuousCoefficients)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A copy of the coefficient group endowed with the discrete topology. -/
def DiscreteGroup (M : Type) := M

instance (M : Type) [AddCommGroup M] : AddCommGroup (DiscreteGroup M) :=
  inferInstanceAs (AddCommGroup M)

instance (M : Type) : TopologicalSpace (DiscreteGroup M) := ⊥

instance (M : Type) : DiscreteTopology (DiscreteGroup M) := ⟨rfl⟩

/-- The additive group is unchanged when the topology is made discrete. -/
def discreteEquiv (M : Type) [AddCommGroup M] : DiscreteGroup M ≃+ M :=
  AddEquiv.refl M

variable (X : Scheme.{0}) [IsLocallyNoetherian X]
variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [T2Space M] [IsTopologicalAddGroup M]

private abbrev D := AddCommGrpCat.of (DiscreteGroup M)

private def chartEquiv (W : X.Etale) : C(W.left, DiscreteGroup M) ≃+ C(W.left, M) where
  toFun f := ⟨fun x ↦ discreteEquiv M (f x),
    continuous_of_discreteTopology.comp f.continuous⟩
  invFun f := ⟨fun x ↦ (discreteEquiv M).symm (f x),
    ((EtaleLocallyConstantHausdorff.of_etaleChart X W f.continuous).comp
      (discreteEquiv M).symm).continuous⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    exact (discreteEquiv M).symm_apply_apply (f x)
  right_inv f := by
    apply ContinuousMap.ext
    intro x
    exact (discreteEquiv M).apply_symm_apply (f x)
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    change discreteEquiv M (f x + g x) = discreteEquiv M (f x) + discreteEquiv M (g x)
    exact map_add (discreteEquiv M) _ _

/-- The actual direct image of continuous Hausdorff-valued functions is
the small étale constant sheaf of the discrete coefficient group. -/
def directImageIso :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj (D M) ≅
      (directImage X).obj (continuousCoefficients X M) := by
  let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{0}
  let e : G.obj (continuousMapSheaf X (D M)) ≅
      G.obj ((directImage X).obj (continuousCoefficients X M)) :=
    NatIso.ofComponents (fun W ↦ (chartEquiv X M W.unop).toAddCommGrpIso) (by
      intro W V f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      apply ContinuousMap.ext
      intro x
      rfl)
  exact constantSheafContinuousMapIso X (D M) ≪≫ G.preimageIso e

/-- The actual pro-étale integral adic sheaf restricts to the constant
underlying p-adic additive group on the small étale site. -/
def adicDirectImageIso (ℓ : ℕ) [Fact ℓ.Prime] :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (DiscreteGroup ℤ_[ℓ])) ≅ (directImage X).obj (X.ellAdicSheaf ℓ) :=
  directImageIso X (AddCommGrpCat.of ℤ_[ℓ])

end
end ManuscriptAudit.EtaleProetaleHausdorffDirectImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleHausdorffDirectImage.directImageIso,
      ``ManuscriptAudit.EtaleProetaleHausdorffDirectImage.adicDirectImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
