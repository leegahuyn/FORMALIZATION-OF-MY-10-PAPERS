import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveConductorClass

/-! The affine nodal H¹ class restricts to zero on the actual Y/Z overlap. -/

namespace ManuscriptAudit.NodalAffineToOverlapHOneZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalProjectiveConductorClass (exists_class_affine_nonzero_chart_zero)
open EtaleOpenIntersection (fstLeg sndLeg intersection_isPullback)
open EtaleTwoOpenHOne (openArrow)
open OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{0}
private abbrev M := AddCommGrpCat.of (ZMod ℓ)
private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology A).obj (M ℓ)

local instance : TopologicalSpace (ZMod ℓ) := ⊥
local instance : DiscreteTopology (ZMod ℓ) := ⟨rfl⟩

/-- Prime-order affine nodal classes vanish after restriction to the actual chart overlap. -/
theorem restriction_eq_zero (h2 : (2 : K) ≠ 0) :
    (((F K ℓ).cohomologyPresheaf 1).map (fstLeg (affineOpen K) (chartOpen K)).op).hom = 0 := by
  let j := affineOpen K
  let k := chartOpen K
  let P := (F K ℓ).cohomologyPresheaf 1
  let a := fstLeg j k
  let b := sndLeg j k
  obtain ⟨z, hZ, hY⟩ := exists_class_affine_nonzero_chart_zero K (M ℓ) h2 1 one_ne_zero
  let t := P.map (openArrow j).op z
  have ht : t ≠ 0 := hZ
  have hSquare : a ≫ openArrow j = b ≫ openArrow k := (intersection_isPullback j k).w
  have ht0 : P.map a.op t = 0 := by
    change P.map a.op (P.map (openArrow j).op z) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hSquare,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    change P.map b.op (P.map (openArrow k).op z) = 0
    rw [show P.map (openArrow k).op z = 0 from hY, map_zero]
  let e₀ := openCohomologyPresheafEquiv j (F K ℓ) 1
  let e₁ := ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app (M ℓ))).addCommGroupIsoToAddEquiv
  let e₂ := (NodalConductorAbelianHOne.affineCyclicHOneEquiv K h2 ℓ).symm
  let e := e₀.trans (e₁.trans e₂)
  have hUnit : e t ≠ 0 := fun h ↦ ht (e.injective (h.trans (map_zero e).symm))
  apply AddMonoidHom.ext
  intro x
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (n := ℓ) (e x / e t)
  have hx : n • t = x := by
    apply e.injective
    rw [map_zsmul, zsmul_eq_mul, hn, div_mul_cancel₀ _ hUnit]
  change (P.map a.op).hom x = 0
  rw [← hx, map_zsmul, show (P.map a.op).hom t = 0 from ht0, smul_zero]

end
end ManuscriptAudit.NodalAffineToOverlapHOneZero

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalAffineToOverlapHOneZero.restriction_eq_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
