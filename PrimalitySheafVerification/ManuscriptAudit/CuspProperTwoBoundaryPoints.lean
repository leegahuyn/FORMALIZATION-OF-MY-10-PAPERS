import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHOne
import PrimalitySheafVerification.ManuscriptAudit.AffineCuspSmoothPuncture

/-! The actual smooth puncture of the fixed proper cusp has exactly the
rational origin and infinity as closed boundary. -/

namespace ManuscriptAudit.CuspProperTwoBoundaryPoints

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp affineOpen projectiveCuspToBase projectiveCusp_isProper)
open CuspNativeCompactSmoothHOne (smoothOpen punctured_range properOrigin_closed)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open SmallEtaleGeometricBaseChange (cuspOrigin cuspPuncturedOpen)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

abbrev origin : Spec (CommRingCat.of K) ⟶ projectiveCusp K := cuspOrigin K ≫ affineOpen K

theorem boundary_disjoint : Disjoint (Set.range (origin K)) (Set.range (infinityPoint K)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ hi
  rw [← CuspInfinitySupport.affine_complement_eq_infinity K] at hi
  exact hi ⟨cuspOrigin K z, rfl⟩

/-- The genuine smooth open is complementary to both displayed rational points. -/
theorem smoothOpen_range :
    Set.range (smoothOpen K) = (Set.range (origin K) ∪ Set.range (infinityPoint K))ᶜ := by
  have ha : Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ := by
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]
  ext x
  change x ∈ Set.range (smoothOpen K) ↔ x ∉ Set.range (origin K) ∪ Set.range (infinityPoint K)
  constructor
  · rintro ⟨y, rfl⟩ h
    rcases h with ⟨z, hz⟩ | hi
    · have hy : (cuspPuncturedOpen K).ι y ∈ Set.range (cuspPuncturedOpen K).ι := ⟨y, rfl⟩
      rw [punctured_range K] at hy
      apply hy
      refine ⟨z, (affineOpen K).isOpenEmbedding.injective ?_⟩
      exact hz
    · have hA : smoothOpen K y ∈ Set.range (affineOpen K) := ⟨(cuspPuncturedOpen K).ι y, rfl⟩
      rw [ha] at hA
      exact hA hi
  · intro hx
    have hA : x ∈ Set.range (affineOpen K) := by
      rw [ha]
      exact fun hI ↦ hx (Or.inr hI)
    obtain ⟨y, rfl⟩ := hA
    have hy : y ∈ Set.range (cuspPuncturedOpen K).ι := by
      rw [punctured_range K]
      rintro ⟨z, hz⟩
      apply hx
      exact Or.inl ⟨z, congrArg (affineOpen K) hz⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, congrArg (affineOpen K) hz⟩

private theorem puncture_affine : IsAffine (cuspPuncturedOpen K).toScheme := by
  have h := (AffineCuspSmoothPuncture.smoothLocus_eq_puncture K).symm.trans
    (AffineCuspSmoothLocus.smoothLocus_eq_basicOpen K)
  rw [h]
  exact IsAffineOpen.Spec_basicOpen (CuspPunctured.cuspSquare K)

/-- The actual open immersion of the smooth puncture is quasi-compact. -/
theorem smoothOpen_quasiCompact : QuasiCompact (smoothOpen K) := by
  letI : IsAffine (cuspPuncturedOpen K).toScheme := puncture_affine K
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiSeparatedSpace (projectiveCusp K) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveCuspToBase K)
  exact quasiCompact_of_compactSpace _

end

end ManuscriptAudit.CuspProperTwoBoundaryPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspProperTwoBoundaryPoints.boundary_disjoint,
      ``ManuscriptAudit.CuspProperTwoBoundaryPoints.smoothOpen_range,
      ``ManuscriptAudit.CuspProperTwoBoundaryPoints.smoothOpen_quasiCompact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
