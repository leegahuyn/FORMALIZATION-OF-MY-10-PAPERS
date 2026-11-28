import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProjectiveNormalizationAffine

/-! The true proper normalization of the cusp is finite and remains a
homeomorphism after every base change, including in characteristics two
and three. -/

namespace ManuscriptAudit.CuspProperNormalizationHomeomorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen affine_chart_cover)
open CuspProjectiveNormalization (normalizationMap normalizationMap_pullback_line_iso)
open CuspProjectiveNormalizationAffine (normalizationAffineIso normalizationAffineIso_inv_over)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private def charts : Bool → Scheme.{u}
  | false => affineCusp K
  | true => Spec (CommRingCat.of (Polynomial K))

private def chartMap : (i : Bool) → charts K i ⟶ projectiveCusp K
  | false => affineOpen K
  | true => lineOpen K

private theorem chartRanges : Set.range (affineOpen K) ∪ Set.range (lineOpen K) = Set.univ :=
  congrArg (fun U : (projectiveCusp K).Opens ↦ (U : Set (projectiveCusp K))) (affine_chart_cover K)

/-- The original two affine charts cover the proper cusp. -/
def chartCover : (projectiveCusp K).OpenCover where
  I₀ := Bool
  X := charts K
  f := chartMap K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      have hx : x ∈ Set.range (affineOpen K) ∪ Set.range (lineOpen K) :=
        (chartRanges K).symm ▸ Set.mem_univ x
      rcases hx with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨false, a, ha⟩
      · exact ⟨true, b, hb⟩
    · intro i
      cases i
      · exact inferInstanceAs (IsOpenImmersion (affineOpen K))
      · exact inferInstanceAs (IsOpenImmersion (lineOpen K))

set_option maxHeartbeats 4700000 in
private theorem of_charts (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.RespectsIso]
    (h₀ : P (CuspScheme.cuspMap K))
    (h₁ : P (pullback.snd (normalizationMap K) (lineOpen K))) :
    P (normalizationMap K) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (chartCover K)]
  intro i
  cases i
  · let e := normalizationAffineIso K
    let p := pullback.snd (normalizationMap K) (affineOpen K)
    change P p
    apply (MorphismProperty.cancel_left_of_respectsIso P e.inv p).mp
    rw [normalizationAffineIso_inv_over K]
    exact h₀
  · exact h₁

/-- The literal proper cusp normalization is a finite morphism. -/
theorem finite : IsFinite (normalizationMap K) := by
  letI := normalizationMap_pullback_line_iso K
  exact of_charts K (@IsFinite) (CuspScheme.paper2_cusp_map_finite K) inferInstance

/-- The literal proper cusp normalization remains injective on all geometric fibers. -/
theorem universallyInjective : UniversallyInjective (normalizationMap K) := by
  letI := normalizationMap_pullback_line_iso K
  exact of_charts K (@UniversallyInjective)
    (CuspScheme.paper2_cusp_map_universally_injective K) inferInstance

/-- The literal proper cusp normalization is surjective. -/
theorem surjective : Surjective (normalizationMap K) := by
  letI := normalizationMap_pullback_line_iso K
  exact of_charts K (@Surjective) (CuspScheme.paper2_cusp_map_surjective K) inferInstance

/-- The actual normalization of the proper cusp is a universal homeomorphism. -/
theorem universalHomeomorphism :
    (topologically @IsHomeomorph).universally (normalizationMap K) := by
  intro X' Y' i₁ i₂ f' h
  letI : IsFinite (normalizationMap K) := finite K
  letI : Surjective f' := of_isPullback h.flip (surjective K)
  letI : UniversallyInjective f' := of_isPullback h.flip (universallyInjective K)
  letI : UniversallyClosed f' :=
    of_isPullback h.flip (inferInstance : UniversallyClosed (normalizationMap K))
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f'.continuous, f'.isClosedMap, ⟨f'.injective, f'.surjective⟩⟩

end
end ManuscriptAudit.CuspProperNormalizationHomeomorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspProperNormalizationHomeomorphism.finite,
      ``ManuscriptAudit.CuspProperNormalizationHomeomorphism.universallyInjective,
      ``ManuscriptAudit.CuspProperNormalizationHomeomorphism.surjective,
      ``ManuscriptAudit.CuspProperNormalizationHomeomorphism.universalHomeomorphism] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
