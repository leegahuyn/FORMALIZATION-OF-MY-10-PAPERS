import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Bochner.Set
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassTraceCurl
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCosetBoundary

/-! Integrating the actual trace curl over the standard fundamental domain equals its coset-cell integral. -/

namespace ManuscriptAudit.Paper8MaassTraceIntegral

open Filter Function MeasureTheory Set UpperHalfPlane
open Paper8MaassTraceCurl Paper8WeightTwoCosetTrace FiniteIndexWeightZeroCosets
open Paper8EtaCosetMass Paper8EtaCosetBoundary
open Paper8EtaPeterssonMass (translate)
open scoped MatrixGroups ModularForm

theorem integral_weightedCurl_trace (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) (J : ℂ → ℂ)
    (hJ : ∀ z : ℍ, DifferentiableAt ℝ J z)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H →
      (fun z : ℍ => J z) ∣[(2 : ℤ)] h = fun z : ℍ => J z)
    (hInt : IntegrableOn (weightedCurl J) (cosetCells H ModularGroup.fdo)) :
    (∫ z in ModularGroup.fdo, weightedCurl (fun w : ℂ =>
      trace H (fun u : ℍ => J u) hInv (ofComplex w)) z) =
      ∫ z in cosetCells H ModularGroup.fdo, weightedCurl J z := by
  letI := rightCosetFintype H
  let S (q : RightCoset H) := translate (cellRepresentative H q) ModularGroup.fdo
  have hE (q : RightCoset H) : MeasurableEmbedding (fun z : ℍ => cellRepresentative H q • z) :=
    measurableEmbedding_const_smul (cellRepresentative H q : GL (Fin 2) ℝ)
  have hM (q : RightCoset H) : MeasurePreserving (fun z : ℍ => cellRepresentative H q • z)
      ((volume : Measure ℍ).restrict ModularGroup.fdo) ((volume : Measure ℍ).restrict (S q)) := by
    have h := measurePreserving_smul (cellRepresentative H q : GL (Fin 2) ℝ) (volume : Measure ℍ)
    exact h.restrict_image_emb (hE q) ModularGroup.fdo
  have hMeas (q : RightCoset H) : MeasurableSet (S q) :=
    (hE q).measurableSet_image.mpr ModularGroup.isOpen_fdo.measurableSet
  have hI (q : RightCoset H) : IntegrableOn (weightedCurl J) (S q) :=
    hInt.mono_set (fun z hz => mem_iUnion.mpr ⟨q, hz⟩)
  have hP (q : RightCoset H) :
      IntegrableOn (fun z => weightedCurl J (cellRepresentative H q • z)) ModularGroup.fdo :=
    (hM q).integrable_comp_of_integrable (hI q)
  calc
    _ = ∫ z in ModularGroup.fdo, ∑ q : RightCoset H, weightedCurl J (cellRepresentative H q • z) :=
      integral_congr_ae (Eventually.of_forall (weightedCurl_trace H J hJ hInv))
    _ = ∑ q : RightCoset H, ∫ z in ModularGroup.fdo, weightedCurl J (cellRepresentative H q • z) :=
      integral_finsetSum Finset.univ (fun q _ => hP q)
    _ = ∑ q : RightCoset H, ∫ z in S q, weightedCurl J z := by
      apply Finset.sum_congr rfl
      intro q _
      exact (hM q).integral_comp (hE q) (weightedCurl J)
    _ = _ := by
      symm
      exact integral_iUnion_fintype hMeas (open_cells_pairwise_disjoint H hNeg) hI

theorem integral_weightedCurl_trace_closed (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) (J : ℂ → ℂ)
    (hJ : ∀ z : ℍ, DifferentiableAt ℝ J z)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H →
      (fun z : ℍ => J z) ∣[(2 : ℤ)] h = fun z : ℍ => J z)
    (hInt : IntegrableOn (weightedCurl J) (cosetCells H ModularGroup.fd)) :
    (∫ z in ModularGroup.fd, weightedCurl (fun w : ℂ =>
      trace H (fun u : ℍ => J u) hInv (ofComplex w)) z) =
      ∫ z in cosetCells H ModularGroup.fd, weightedCurl J z := by
  have hFD : ModularGroup.fd =ᵐ[(volume : Measure ℍ)] ModularGroup.fdo :=
    ae_eq_set.mpr ⟨volume_fd_boundary_zero, by simp [sdiff_eq_empty.mpr ModularGroup.fdo_subset_fd]⟩
  have hSub : cosetCells H ModularGroup.fdo ⊆ cosetCells H ModularGroup.fd := by
    intro z hz
    obtain ⟨q, u, hu, rfl⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨q, u, ModularGroup.fdo_subset_fd hu, rfl⟩
  rw [setIntegral_congr_set hFD, setIntegral_congr_set (closed_cells_ae_eq_open H)]
  exact integral_weightedCurl_trace H hNeg J hJ hInv (hInt.mono_set hSub)

end ManuscriptAudit.Paper8MaassTraceIntegral

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassTraceIntegral.integral_weightedCurl_trace_closed
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
