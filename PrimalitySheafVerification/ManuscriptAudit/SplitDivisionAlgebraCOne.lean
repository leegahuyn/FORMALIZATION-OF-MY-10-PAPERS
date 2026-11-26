import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Dimension.Constructions
import PrimalitySheafVerification.ManuscriptAudit.DivisionAlgebraDeterminantForm
import PrimalitySheafVerification.ManuscriptAudit.DivisionAlgebraSplitTwist
import PrimalitySheafVerification.ManuscriptAudit.GaloisInvariantPolynomial
import PrimalitySheafVerification.ManuscriptAudit.MatrixAlgebraDeterminant

/-!
# A division algebra split by a finite Galois extension of a C1 field

The matrix determinant of a generic division algebra element descends
to the base field. Its anisotropy and the C1 property bound the number
of basis vectors by the size of the matrix realization.
-/

namespace ManuscriptAudit.SplitDivisionAlgebraCOne

open MvPolynomial DivisionAlgebraDeterminantForm DivisionAlgebraSplitTwist
open scoped TensorProduct

noncomputable section

variable {F L D : Type*} [Field F] [Field L] [Algebra F L]
  [DivisionRing D] [Algebra F D] {m n : ℕ}

/-- Galois automorphisms fix the coefficients of the determinant form
arising from a splitting. -/
theorem determinantForm_invariant [Infinite L]
    (s : L ⊗[F] D ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (b : Module.Basis (Fin m) F D) (τ : L ≃ₐ[F] L) :
    map τ.toRingHom (determinantForm b (representation s)) =
      determinantForm b (representation s) := by
  let r := representation s
  have hQ := determinantForm_homogeneous b r
  apply (hQ.map τ.toRingHom).funext hQ
  intro z
  rw [eval_map_determinantForm]
  have hright : eval z (determinantForm b r) = (∑ i : Fin m, z i • r (b i)).det := by
    simpa only [map_id, RingHom.mapMatrix_id, RingHom.id_apply] using
      (eval_map_determinantForm b r (RingHom.id L) z)
  rw [hright]
  have hM : (∑ i : Fin m, z i • τ.toRingHom.mapMatrix (r (b i))) =
      splitTwist s τ (∑ i : Fin m, z i • r (b i)) := by
    simp only [map_sum, map_smul, r, splitTwist_representation]
  rw [hM, MatrixAlgebraDeterminant.det_map]

set_option maxHeartbeats 1200000 in
/-- A finite-dimensional division algebra over a C1 field has rank one
if it splits over an infinite, finite Galois extension of the field. -/
theorem finrank_eq_one [FiniteDimensional F D] [FiniteDimensional F L] [IsGalois F L]
    [Infinite L] (s : L ⊗[F] D ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (hC : ∀ {a d : ℕ} (P : MvPolynomial (Fin a) F), P.IsHomogeneous d →
      0 < d → d < a → ∃ z : Fin a → F, z ≠ 0 ∧ aeval z P = 0) :
    Module.finrank F D = 1 := by
  let m := Module.finrank F D
  let b : Module.Basis (Fin m) F D := Module.finBasis F D
  let r := representation s
  let Q := determinantForm b r
  have hDim : m = n * n := by
    have h := s.toLinearEquiv.finrank_eq
    simpa [Module.finrank_baseChange, Module.finrank_matrix, m] using h
  have hm : 0 < m := Module.finrank_pos
  have hn : 0 < n := by
    by_contra! h
    have hzero : n = 0 := Nat.eq_zero_of_le_zero h
    exact (Nat.ne_of_gt hm) (hDim.trans (by simp [hzero]))
  obtain ⟨P, hP, hPQ⟩ :=
    GaloisInvariantPolynomial.exists_homogeneous_map_eq Q (determinantForm_homogeneous b r)
      (determinantForm_invariant s b)
  have hBound : m ≤ n := by
    by_contra! h
    obtain ⟨z, hz, hZ⟩ := hC P hP hn h
    apply hz
    apply determinantForm_anisotropic b r
    change aeval (fun i ↦ algebraMap F L (z i)) Q = 0
    rw [← hPQ, GaloisInvariantPolynomial.aeval_map_algebraMap, hZ, map_zero]
  have hle : n * n ≤ n := by rwa [← hDim]
  have hOne : n = 1 := by
    by_contra h
    have hlt : 1 < n := by omega
    have habs : n < n * n := by simpa using Nat.mul_lt_mul_of_pos_left hlt hn
    exact (Nat.not_lt_of_ge hle) habs
  exact hDim.trans (by simp [hOne])

end

end ManuscriptAudit.SplitDivisionAlgebraCOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SplitDivisionAlgebraCOne.determinantForm_invariant,
      ``ManuscriptAudit.SplitDivisionAlgebraCOne.finrank_eq_one] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
