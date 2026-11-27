import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCuspSmoothLocus
import PrimalitySheafVerification.ManuscriptAudit.CuspOpenOriginSequence

/-! The actual relative smooth open of the affine cusp is the puncture in the compact-support sequence. -/

namespace ManuscriptAudit.AffineCuspSmoothPuncture

open AlgebraicGeometry CategoryTheory
open CuspPunctured (CuspSubalgebra cuspSquare)
open CuspDelta (cuspOriginResidue paper2_cusp_origin_isMaximal
  paper2_cusp_conductor_comap_eq_origin paper2_cusp_conductor_eq_square)
open CuspScheme (cuspMap paper2_cusp_map_surjective)
open SmallEtaleGeometricBaseChange (cuspOrigin cuspPuncturedOpen)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev cusp := AffineCuspSmoothLocus.cusp K

private theorem square_residue_zero : cuspOriginResidue K (cuspSquare K) = 0 := by
  change Polynomial.constantCoeff ((Polynomial.X : Polynomial K) ^ 2) = 0
  simp

private theorem origin_ideal_le {x : cusp K} (hx : cuspSquare K ∈ x.asIdeal) :
    RingHom.ker (cuspOriginResidue K) ≤ x.asIdeal := by
  have h := paper2_cusp_map_surjective K
  rw [surjective_iff] at h
  obtain ⟨z, hz⟩ := h x
  have hIdeal : Ideal.comap (algebraMap (CuspSubalgebra K) (Polynomial K)) z.asIdeal =
      x.asIdeal := by
    rw [cuspMap, Spec.map_apply] at hz
    exact congrArg PrimeSpectrum.asIdeal hz
  have hzSquare : (Polynomial.X : Polynomial K) ^ 2 ∈ z.asIdeal := by
    rw [← hIdeal] at hx
    exact hx
  rw [← paper2_cusp_conductor_comap_eq_origin, paper2_cusp_conductor_eq_square, ← hIdeal]
  exact Ideal.comap_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hzSquare))

private theorem square_mem_iff_origin (x : cusp K) :
    cuspSquare K ∈ x.asIdeal ↔ x ∈ Set.range (cuspOrigin K) := by
  constructor
  · intro hx
    have hm := paper2_cusp_origin_isMaximal K
    have he : RingHom.ker (cuspOriginResidue K) = x.asIdeal :=
      hm.eq_of_le x.isPrime.ne_top (origin_ideal_le K hx)
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (cuspOriginResidue K) (IsLocalRing.maximalIdeal K) = x.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact he
  · rintro ⟨z, rfl⟩
    change cuspOriginResidue K (cuspSquare K) ∈ z.asIdeal
    rw [square_residue_zero]
    exact Ideal.zero_mem _

/-- The relative smooth open is exactly the puncture used in the native localization sequence. -/
theorem smoothLocus_eq_puncture :
    (AffineCuspSmoothLocus.cuspToBase K).smoothLocus = cuspPuncturedOpen K := by
  rw [AffineCuspSmoothLocus.smoothLocus_eq_basicOpen]
  ext x
  change x ∈ PrimeSpectrum.basicOpen (cuspSquare K) ↔ x ∈ (Set.range (cuspOrigin K))ᶜ
  rw [PrimeSpectrum.mem_basicOpen, Set.mem_compl_iff]
  exact not_congr (square_mem_iff_origin K x)

end
end ManuscriptAudit.AffineCuspSmoothPuncture

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineCuspSmoothPuncture.smoothLocus_eq_puncture
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
