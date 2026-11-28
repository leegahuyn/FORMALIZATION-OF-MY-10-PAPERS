import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombHessianCompression
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsEigenbasis

/-! Restricting a closed form to a closed Hilbert subspace preserves the
genuine compact inclusion and identifies the required density condition. -/

namespace ManuscriptAudit.Paper10ClosedSliceFormDomain

open Paper10FriedrichsResolvent Paper10FriedrichsEigenbasis

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (J : D →L[ℝ] H) (S : Submodule ℝ H)

abbrev FormSlice := S.comap J.toLinearMap

theorem isClosed_formSlice (hS : IsClosed (S : Set H)) :
    IsClosed (FormSlice J S : Set D) :=
  hS.preimage J.continuous

theorem complete_formSlice [CompleteSpace D] (hS : IsClosed (S : Set H)) :
    CompleteSpace (FormSlice J S) :=
  completeSpace_coe_iff_isComplete.mpr (isClosed_formSlice J S hS).isComplete

variable [S.HasOrthogonalProjection]

/-- On the form slice the compressed inclusion is the original inclusion. -/
def inclusion : FormSlice J S →L[ℝ] S :=
  S.orthogonalProjectionOnto ∘L (J ∘L (FormSlice J S).subtypeL)

theorem inclusion_coe (u : FormSlice J S) : (inclusion J S u : H) = J u := by
  let v : S := ⟨J u, u.property⟩
  exact congrArg Subtype.val (S.orthogonalProjectionOnto_mem_subspace_eq_self v)

theorem inclusion_isCompact (hJ : IsCompactOperator J) : IsCompactOperator (inclusion J S) :=
  (hJ.comp_clm (FormSlice J S).subtypeL).clm_comp S.orthogonalProjectionOnto

theorem inclusion_injective (hJ : Function.Injective J) : Function.Injective (inclusion J S) := by
  intro u v h
  apply Subtype.ext
  apply hJ
  simpa only [inclusion_coe] using congrArg Subtype.val h

/-- Preservation of the original form domain by the Hilbert projection yields
a dense form domain in the genuine closed slice. -/
theorem inclusion_denseRange (hJ : DenseRange J)
    (hPreserves : ∀ u, (S.orthogonalProjectionOnto (J u) : H) ∈ Set.range J) :
    DenseRange (inclusion J S) := by
  have hP : Function.Surjective S.orthogonalProjectionOnto := by
    intro v
    exact ⟨v, S.orthogonalProjectionOnto_mem_subspace_eq_self v⟩
  have hd := hP.denseRange.comp hJ S.orthogonalProjectionOnto.continuous
  apply hd.mono
  rintro v ⟨u,rfl⟩
  obtain ⟨w, hw⟩ := hPreserves u
  let w' : FormSlice J S := ⟨w, by
    change J w ∈ S
    rw [hw]
    exact (S.orthogonalProjectionOnto (J u)).property⟩
  refine ⟨w', Subtype.ext ?_⟩
  rw [inclusion_coe]
  exact hw

open scoped RealInnerProductSpace

/-- The closed slice has an actual self-adjoint realization of its restricted
form and an orthonormal basis of true operator eigenvectors. -/
theorem slice_selfAdjoint_eigenbasis [CompleteSpace D] [CompleteSpace S]
    (hS : IsClosed (S : Set H)) (hJ : DenseRange J) (hK : IsCompactOperator J)
    (hPreserves : ∀ u, (S.orthogonalProjectionOnto (J u) : H) ∈ Set.range J) :
    ∃ (T : S →ₗ.[ℝ] S) (I : Type) (value : I → ℝ) (basis : HilbertBasis I ℝ S),
      IsSelfAdjoint T ∧
      (∀ x y, (x,y) ∈ T.graph ↔ ∃ u : FormSlice J S, inclusion J S u = x ∧
        ∀ w : FormSlice J S, ⟪u,w⟫ = ⟪y,inclusion J S w⟫) ∧
      (∀ i, (basis i,value i • basis i) ∈ T.graph) := by
  letI : CompleteSpace (FormSlice J S) := complete_formSlice J S hS
  let J' := inclusion J S
  have hd : DenseRange J' := inclusion_denseRange J S hJ hPreserves
  have hk : IsCompactOperator J' := inclusion_isCompact J S hK
  obtain ⟨b,hb⟩ := exists_eigenbasis J' hd hk
  exact ⟨realization J', EigenIndex J', fun i => i.1, b, realization_selfAdjoint J' hd,
    realization_form_iff J' hd, hb⟩

end
end ManuscriptAudit.Paper10ClosedSliceFormDomain

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10ClosedSliceFormDomain.complete_formSlice,
      ``ManuscriptAudit.Paper10ClosedSliceFormDomain.inclusion_isCompact,
      ``ManuscriptAudit.Paper10ClosedSliceFormDomain.inclusion_denseRange,
      ``ManuscriptAudit.Paper10ClosedSliceFormDomain.slice_selfAdjoint_eigenbasis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
