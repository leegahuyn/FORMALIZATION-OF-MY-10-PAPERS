import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportExcess
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportProjectiveComparison
import PrimalitySheafVerification.ManuscriptAudit.CuspProperYChart
import PrimalitySheafVerification.ManuscriptAudit.CuspSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.EtaleOpenIntersection
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne

/-!
# Absolute degree-one compactly supported cohomology of the cusp

On the actual two-open cover of the proper cusp the affine cusp
and affine line have zero ordinary cyclic-coefficient H¹. The
nonempty connected overlap allows degree-one descent. Localization
at infinity then computes Hc¹ of the affine cusp, and localization
at the origin computes Hc¹ of the puncture.
-/

namespace ManuscriptAudit.CuspCompactSupportAbsoluteHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification CuspProperYChart CuspCompactSupportSequence

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (ℓ : ℕ) [NeZero (ℓ : K)]

private abbrev coeff : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod ℓ)

private abbrev C (S : Scheme.{0}) :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{0}).obj (coeff ℓ)

/-- Ordinary degree-one cyclic cohomology of the actual proper cusp vanishes. -/
theorem projectiveCusp_HOne_subsingleton : Subsingleton (Sheaf.H (C ℓ (projectiveCusp K)) 1) := by
  let f := affineOpen K
  let g := lineOpen K
  letI : IsOpenImmersion f := affineOpen_isOpenImmersion K
  letI : IsOpenImmersion g := lineOpen_isOpenImmersion K
  let h := pullback.fst f g ≫ f
  letI : IsOpenImmersion h := inferInstanceAs (IsOpenImmersion (pullback.fst f g ≫ f))
  have hCov : Set.range f ∪ Set.range g = Set.univ := by
    exact congrArg (fun O : (projectiveCusp K).Opens => (O : Set (projectiveCusp K)))
      (affine_chart_cover K)
  have hConn : IsConnected (Set.range h) := by
    change IsConnected (Set.range (pullback.fst f g ≫ f))
    rw [Scheme.Pullback.range_fst_comp]
    exact affine_chart_overlap_isConnected K
  letI : Nonempty (pullback f g) := by
    obtain ⟨x, y, _⟩ := hConn.nonempty
    exact ⟨y⟩
  letI : PreconnectedSpace (pullback f g) := by
    apply preconnectedSpace_iff_univ.mpr
    apply (h.isOpenEmbedding.isInducing.isPreconnected_image).mp
    simpa only [Set.image_univ] using hConn.isPreconnected
  exact EtaleOpenIntersection.ambientHOne_subsingleton f g (coeff ℓ) hCov
    (CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton K p ℓ)
    (SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K ℓ)

/-- Native Hc¹ of the affine cusp vanishes with the specified coefficients. -/
theorem cuspHcOne_subsingleton : Subsingleton (cuspHc K (coeff ℓ) 1) := by
  let e := cuspHcSuccProjectiveEquiv K (coeff ℓ) 0
  have h := projectiveCusp_HOne_subsingleton K p ℓ
  exact ⟨fun a b => e.injective (h.allEq (e a) (e b))⟩

/-- Native Hc¹ of the punctured cusp is exactly one cyclic coefficient group. -/
def punctureHcOneEquiv : punctureHc K (coeff ℓ) 1 ≃+ ZMod ℓ := by
  let f := Sheaf.H.map (compactSupportSequence K (coeff ℓ)).f 1
  let h := cuspHcOne_subsingleton K p ℓ
  let e : punctureHc K (coeff ℓ) 1 ≃+ f.ker :=
    { toFun := fun x => ⟨x, h.allEq _ _⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  exact e.trans (CuspCompactSupportExcess.firstKernelEquivOrigin K (coeff ℓ))

end

end ManuscriptAudit.CuspCompactSupportAbsoluteHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportAbsoluteHOne.projectiveCusp_HOne_subsingleton,
      ``ManuscriptAudit.CuspCompactSupportAbsoluteHOne.cuspHcOne_subsingleton,
      ``ManuscriptAudit.CuspCompactSupportAbsoluteHOne.punctureHcOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
