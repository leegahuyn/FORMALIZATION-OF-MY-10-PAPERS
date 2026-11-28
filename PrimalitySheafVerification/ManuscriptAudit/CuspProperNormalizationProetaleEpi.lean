import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProperNormalizationHomeomorphism
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizedNativeCharts
import PrimalitySheafVerification.ManuscriptAudit.CuspProetaleAffineEquivalence
import PrimalitySheafVerification.ManuscriptAudit.AffineProetaleBaseChangeEquivalence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestrictionEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageIdentity
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageRestrictionPullback

/-! Exact native pro-étale direct image of the actual proper cusp normalization. -/

namespace ManuscriptAudit.CuspProperNormalizationProetaleEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (affineOpen)
open CuspProperYChart (lineOpen)
open CuspProjectiveNormalization (normalizedCusp normalizationMap)
open CuspNormalizedNativeCharts (affineInclusion lineInclusion affine_isPullback line_isPullback)
open CuspProperNormalizationHomeomorphism (chartCover)
open ProetaleBaseChange (directImage)
open ProetaleObjectRestriction (restriction restrictionAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

private theorem restrict_epi {X Y U V : Scheme.{0}} {f : Y ⟶ X} {j : U ⟶ X}
    {p : V ⟶ Y} {q : V ⟶ U} [WeaklyEtale j] [WeaklyEtale p]
    (H : IsPullback p q f j) {F G : P Y} (α : F ⟶ G)
    (h : Epi ((directImage q A).map ((restriction p A).map α))) :
    Epi ((restriction j A).map ((directImage f A).map α)) := by
  let e := ProetaleDirectImageRestrictionPullback.directImageRestrictionIso H
  letI := h
  apply (epi_comp_iff_of_isIso _ (e.hom.app G)).mp
  change Epi (((directImage f A ⋙ restriction j A).map α) ≫ e.hom.app G)
  rw [e.hom.naturality]
  infer_instance

variable (K : Type) [Field K] (p : ℕ) [hp : Fact p.Prime] [hchar : CharP K p]

include p hp hchar

private theorem affine_map_epi
    {F G : P (CuspProetaleAffineEquivalence.Normalization K)} (α : F ⟶ G) [Epi α] :
    Epi ((directImage (CuspScheme.cuspMap K) A).map α) := by
  let f := CuspScheme.cuspMap K
  letI : Surjective f := CuspScheme.paper2_cusp_map_surjective K
  letI : (AffineProetaleSite.baseChange f).IsEquivalence :=
    CuspProetaleAffineEquivalence.normalizationIsEquivalence K p
  letI : (directImage f A).IsEquivalence :=
    AffineProetaleBaseChangeEquivalence.directImage_isEquivalence f
  exact (directImage f A).map_epi α

set_option maxHeartbeats 7200000 in
/-- Pullback to both affine charts detects exact direct image on the proper cusp. -/
theorem map_epi {F G : P (normalizedCusp K)} (α : F ⟶ G) [Epi α] :
    Epi ((directImage (normalizationMap K) A).map α) := by
  apply ProetaleOpenRestrictionEpi.epi_of_openCover (chartCover K)
  intro i
  cases i
  · change Epi ((restriction (affineOpen K) A).map
      ((directImage (normalizationMap K) A).map α))
    let u := affineInclusion K
    letI : (restriction u A).IsLeftAdjoint := (restrictionAdjunction u A).isLeftAdjoint
    letI : Epi ((restriction u A).map α) := (restriction u A).map_epi α
    exact restrict_epi (affine_isPullback K) α (affine_map_epi K p ((restriction u A).map α))
  · change Epi ((restriction (lineOpen K) A).map
      ((directImage (normalizationMap K) A).map α))
    let u := lineInclusion K
    letI : (restriction u A).IsLeftAdjoint := (restrictionAdjunction u A).isLeftAdjoint
    letI : Epi ((restriction u A).map α) := (restriction u A).map_epi α
    exact restrict_epi (line_isPullback K) α
      (ProetaleDirectImageIdentity.map_epi _ ((restriction u A).map α))

end
end ManuscriptAudit.CuspProperNormalizationProetaleEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspProperNormalizationProetaleEpi.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
