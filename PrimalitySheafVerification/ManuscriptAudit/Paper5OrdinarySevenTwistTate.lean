import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTwistGeometry
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenRotatedTate

/-! The complete characteristic-seven table on the actual 2-adic and 3-adic Tate modules. -/

namespace ManuscriptAudit.Paper5OrdinarySevenTwistTate

open Polynomial Module CubicThreeTorsionOrdinate CubicFrobeniusScaling Paper5OrdinarySeven
open Paper5OrdinarySevenFrobenius Paper5OrdinarySevenTwistParameters Paper5OrdinarySevenTwistGeometry
open Paper5OrdinarySevenRotatedTate PowerTateModule

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev Geometric (A : ZMod 7) := (Curve (algebraMap (ZMod 7) L A)).Point

abbrev action (A : ZMod 7) : Module.End ℤ_[l] (Tate l (Geometric L A)) :=
  endMap l (nativeMap (ZMod 7) L (FiniteField.frobeniusAlgHom (ZMod 7) L) A)

private def refOperator (A : ZMod 7) : AddMonoid.End (Points L) :=
  signedRotation L (row A) * nativeFrobenius L

private def e (A : ZMod 7) (hA : A ≠ 0) : Points L ≃+ Geometric L A :=
  (exists_conjugacy L A hA).choose

private def eTate (A : ZMod 7) (hA : A ≠ 0) : Tate l (Points L) ≃ₗ[ℤ_[l]] Tate l (Geometric L A) :=
  mapAddEquiv l (e L A hA)

private theorem tate_conjugacy (A : ZMod 7) (hA : A ≠ 0) :
    (eTate L l A hA).conj (endMap l (refOperator L A)) = action L l A := by
  have h (v : Tate l (Points L)) :
      action L l A (eTate L l A hA v) = eTate L l A hA (endMap l (refOperator L A) v) := by
    apply PowerTateModule.ext l (Geometric L A)
    intro n
    apply Subtype.ext
    exact (exists_conjugacy L A hA).choose_spec (evaluate l (Points L) n v : Points L)
  apply LinearMap.ext
  intro x
  change eTate L l A hA (endMap l (refOperator L A) ((eTate L l A hA).symm x)) = action L l A x
  rw [← h, (eTate L l A hA).apply_symm_apply]

def tateBasis (hl : l = 2 ∨ l = 3) (A : ZMod 7) (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[l] (Tate l (Geometric L A)) :=
  (Paper5OrdinarySevenTate.tateBasis L l hl).map (eTate L l A hA)

private theorem ref_trace_det (hl : l = 2 ∨ l = 3) (A : ZMod 7) (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (endMap l (refOperator L A)) = ((row A).trace : ℤ_[l]) ∧
      LinearMap.det (endMap l (refOperator L A)) = 7 := by
  let B := Paper5OrdinarySevenTate.tateBasis L l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let T := rotatedAction L l (row A).exponent
  obtain ⟨ht, hd⟩ := Paper5OrdinarySevenRotatedTate.trace_det L l hl (row A).exponent
  have hRow := (row_parameters A hA).2.2.2.2
  have hDim : Module.finrank ℤ_[l] (Tate l (Points L)) = 2 := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  cases h : (row A).negate
  · have he : endMap l (refOperator L A) = T := by
      simp [refOperator, signedRotation, h, T, rotatedAction, rotationAction, Paper5OrdinarySevenTate.action]
    have htrace : (row A).trace = rotatedTrace (row A).exponent := by simpa [h] using hRow
    rw [he, htrace]
    exact ⟨ht, hd⟩
  · have he : endMap l (refOperator L A) = -T := by
      simp [refOperator, signedRotation, h, T, rotatedAction, rotationAction,
        Paper5OrdinarySevenTate.action]
      apply LinearMap.ext
      intro x
      rfl
    have htrace : (row A).trace = -rotatedTrace (row A).exponent := by simpa [h] using hRow
    rw [he, htrace, Int.cast_neg]
    constructor
    · have hNeg := map_neg (LinearMap.trace ℤ_[l] (Tate l (Points L))) T
      rw [hNeg, ht]
    · rw [← neg_one_smul (ℤ_[l]) T, LinearMap.det_smul, hDim, hd]
      norm_num

/-- The six twists have traces −4, −1, −5, 5, 1, 4 and determinant seven. -/
theorem trace_det (hl : l = 2 ∨ l = 3) (A : ZMod 7) (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric L A)) (action L l A) = ((row A).trace : ℤ_[l]) ∧
      LinearMap.det (action L l A) = 7 := by
  rw [← tate_conjugacy L l A hA]
  obtain ⟨ht, hd⟩ := ref_trace_det L l hl A hA
  refine ⟨(LinearMap.trace_conj' _ _).trans ht, ?_⟩
  let E := eTate L l A hA
  let R := endMap l (refOperator L A)
  have hConj : E.conj R = E.toLinearMap ∘ₗ R ∘ₗ E.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hConj]
  exact (LinearMap.det_conj R E).trans hd

theorem charpoly (hl : l = 2 ∨ l = 3) (A : ZMod 7) (hA : A ≠ 0) :
    letI := Module.Free.of_basis (tateBasis L l hl A hA)
    letI := Module.Finite.of_basis (tateBasis L l hl A hA)
    (action L l A).charpoly = X ^ 2 - C ((row A).trace : ℤ_[l]) * X + C (7 : ℤ_[l]) := by
  let B := tateBasis L l hl A hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl A hA
  change (action L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end
end ManuscriptAudit.Paper5OrdinarySevenTwistTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenTwistTate.tateBasis,
      ``ManuscriptAudit.Paper5OrdinarySevenTwistTate.trace_det,
      ``ManuscriptAudit.Paper5OrdinarySevenTwistTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
