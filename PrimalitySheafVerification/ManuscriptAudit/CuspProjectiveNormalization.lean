import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Normalization
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersection

/-! The proper cusp's native relative normalization is taken along its
regular affine line chart. It is unchanged on that chart. -/

namespace ManuscriptAudit.CuspProjectiveNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp projectiveCuspToBase projectiveCusp_isProper)
open CuspProperYChart (lineOpen)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

instance lineOpen_quasiCompact : QuasiCompact (lineOpen K) := by
  letI := projectiveCusp_isProper K
  letI : QuasiSeparatedSpace (projectiveCusp K) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveCuspToBase K)
  exact quasiCompact_of_compactSpace (lineOpen K)

/-- Native relative normalization of the proper cusp along the nonsingular chart. -/
abbrev normalizedCusp : Scheme.{u} := (lineOpen K).normalization

/-- The original integral morphism from the actual proper normalization. -/
def normalizationMap : normalizedCusp K ⟶ projectiveCusp K :=
  (lineOpen K).fromNormalization

theorem normalizationMap_integral : IsIntegralHom (normalizationMap K) :=
  inferInstanceAs (IsIntegralHom (lineOpen K).fromNormalization)

theorem inclusion_factors :
    (lineOpen K).toNormalization ≫ normalizationMap K = lineOpen K :=
  (lineOpen K).toNormalization_fromNormalization

private instance lineSelfPullback_iso :
    IsIso (pullback.snd (lineOpen K) (lineOpen K)) := by
  let p := pullback.snd (lineOpen K) (lineOpen K)
  let t : Spec (CommRingCat.of (Polynomial K)) ⟶ pullback (lineOpen K) (lineOpen K) :=
    pullback.lift (𝟙 _) (𝟙 _) rfl
  have ht : t ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  refine ⟨⟨t, ?_, ht⟩⟩
  apply (cancel_mono p).mp
  rw [Category.assoc, ht, Category.comp_id, Category.id_comp]

set_option maxHeartbeats 3700000 in
/-- Normalization is an isomorphism on the regular affine line chart. -/
theorem normalizationMap_pullback_line_iso :
    IsIso (pullback.snd (normalizationMap K) (lineOpen K)) := by
  let f := lineOpen K
  let p := pullback.snd f f
  letI : IsIso p := lineSelfPullback_iso K
  letI : IsIso p.toNormalization := inferInstance
  have h : p.fromNormalization = inv p.toNormalization ≫ p :=
    (IsIso.eq_inv_comp p.toNormalization).mpr p.toNormalization_fromNormalization
  letI : IsIso p.fromNormalization :=
    h.symm ▸ inferInstanceAs (IsIso (inv p.toNormalization ≫ p))
  letI : Smooth f := inferInstance
  letI : IsIso (f.normalizationPullback f) := inferInstance
  have h' : pullback.snd f.fromNormalization f = inv (f.normalizationPullback f) ≫
      p.fromNormalization :=
    (IsIso.eq_inv_comp (f.normalizationPullback f)).mpr (f.normalizationPullback_snd f)
  change IsIso (pullback.snd f.fromNormalization f)
  rw [h']
  infer_instance

def normalizationLineIso :
    pullback (normalizationMap K) (lineOpen K) ≅ Spec (CommRingCat.of (Polynomial K)) := by
  letI := normalizationMap_pullback_line_iso K
  exact asIso (pullback.snd (normalizationMap K) (lineOpen K))

end
end ManuscriptAudit.CuspProjectiveNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspProjectiveNormalization.normalizationMap_integral,
      ``ManuscriptAudit.CuspProjectiveNormalization.inclusion_factors,
      ``ManuscriptAudit.CuspProjectiveNormalization.normalizationMap_pullback_line_iso,
      ``ManuscriptAudit.CuspProjectiveNormalization.normalizationLineIso] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
