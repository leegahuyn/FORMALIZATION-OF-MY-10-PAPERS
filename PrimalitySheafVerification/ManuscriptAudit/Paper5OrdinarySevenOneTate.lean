import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenOneTwist
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTate

/-! The printed characteristic-seven fiber has actual Tate polynomial T²+4T+7 at 2 and 3. -/

namespace ManuscriptAudit.Paper5OrdinarySevenOneTate

open Polynomial Module WeierstrassCurve CubicThreeTorsionOrdinate CubicFrobeniusScaling
open Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenOneTwist
open PowerTateModule RankTwoQuadraticOperator

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev Geometric := (Curve (algebraMap (ZMod 7) L 1)).Point

private def e : Points L ≃+ Geometric L := (exists_frobenius_conjugacy L).choose

private def refOperator : AddMonoid.End (Points L) :=
  -(3 : AddMonoid.End (Points L)) - (2 : ℕ) • rotation L

private theorem refOperator_apply (P : Points L) :
    refOperator L P = -((3 : ℕ) • P) - (2 : ℕ) • rotation L P := rfl

abbrev nativeOperator : AddMonoid.End (Geometric L) :=
  nativeMap (ZMod 7) L (FiniteField.frobeniusAlgHom (ZMod 7) L) 1

abbrev action : Module.End ℤ_[l] (Tate l (Geometric L)) := endMap l (nativeOperator L)

private def eTate : Tate l (Points L) ≃ₗ[ℤ_[l]] Tate l (Geometric L) := mapAddEquiv l (e L)

private theorem tate_conjugacy :
    (eTate L l).conj (endMap l (refOperator L)) = action L l := by
  have h (v : Tate l (Points L)) :
      action L l (eTate L l v) = eTate L l (endMap l (refOperator L) v) := by
    apply PowerTateModule.ext l (Geometric L)
    intro n
    apply Subtype.ext
    exact (exists_frobenius_conjugacy L).choose_spec (evaluate l (Points L) n v : Points L)
  apply LinearMap.ext
  intro x
  change eTate L l (endMap l (refOperator L) ((eTate L l).symm x)) = action L l x
  rw [← h, (eTate L l).apply_symm_apply]

private theorem point_quad :
    refOperator L ^ 2 + (4 : AddMonoid.End (Points L)) * refOperator L + 7 = 0 := by
  have hR (P : Points L) : rotation L (rotation L P) = -P - rotation L P := by
    calc
      _ = (rotation L P + rotation L (rotation L P)) - rotation L P := by abel
      _ = _ := by rw [rotation_sum]
  apply AddMonoidHom.ext
  intro P
  change refOperator L (refOperator L P) + (4 : ℕ) • refOperator L P + (7 : ℕ) • P = 0
  rw [refOperator_apply, refOperator_apply]
  simp only [map_sub, map_neg, map_nsmul, hR]
  abel

/-- The actual native (7)-power map satisfies its fixed quadratic identity on all points. -/
theorem native_quadratic :
    nativeOperator L ^ 2 + (4 : AddMonoid.End (Geometric L)) * nativeOperator L + 7 = 0 := by
  apply AddMonoidHom.ext
  intro Q
  obtain ⟨P, rfl⟩ := (e L).surjective Q
  have hE (V : Points L) : nativeOperator L (e L V) = e L (refOperator L V) := by
    rw [refOperator_apply]
    exact (exists_frobenius_conjugacy L).choose_spec V
  have h := congrArg (fun m : AddMonoid.End (Points L) => m P) (point_quad L)
  change refOperator L (refOperator L P) + (4 : ℕ) • refOperator L P + (7 : ℕ) • P = 0 at h
  change nativeOperator L (nativeOperator L (e L P)) + (4 : ℕ) • nativeOperator L (e L P) +
    (7 : ℕ) • e L P = 0
  rw [hE, hE, ← map_nsmul, ← map_nsmul, ← map_add, ← map_add, h, map_zero]

/-- The actual action satisfies the same identity on every prime-adic Tate module. -/
theorem tate_quadratic :
    action L l ^ 2 + (4 : Module.End ℤ_[l] (Tate l (Geometric L))) * action L l + 7 = 0 := by
  simpa only [map_add, map_mul, map_pow, map_ofNat, map_zero] using
    congrArg (endMap l) (native_quadratic L)

def tateBasis (hl : l = 2 ∨ l = 3) : Basis (Fin 2) ℤ_[l] (Tate l (Geometric L)) :=
  (Paper5OrdinarySevenTate.tateBasis L l hl).map (eTate L l)

private theorem ref_trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (endMap l (refOperator L)) = -4 ∧
      LinearMap.det (endMap l (refOperator L)) = 7 := by
  let B := Paper5OrdinarySevenTate.tateBasis L l hl
  let T := endMap l (refOperator L)
  let S := endMap l (rotation L)
  let I : Module.End ℤ_[l] (Tate l (Points L)) := 1
  have hT : T = -(3 : Module.End ℤ_[l] (Tate l (Points L))) - (2 : ℤ_[l]) • S := by
    change _ = -(3 : Module.End ℤ_[l] (Tate l (Points L))) - ((2 : ℕ) : ℤ_[l]) • S
    rw [Nat.cast_smul_eq_nsmul]
    simp only [T, S, refOperator, map_sub, map_neg, map_ofNat, map_nsmul]
  have hN : ¬∃ c : ℤ_[l], T = c • I := by
    rintro ⟨c, hc⟩
    have hThree : (3 : ℤ_[l]) • I = (3 : Module.End ℤ_[l] (Tate l (Points L))) := by
      change (3 : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (Points L))) = _
      rw [← Algebra.algebraMap_eq_smul_one, map_ofNat]
    have hRel : (c + 3) • I + (2 : ℤ_[l]) • S = 0 := by
      rw [add_smul, hThree]
      calc
        _ = c • I - (-(3 : Module.End ℤ_[l] (Tate l (Points L))) - (2 : ℤ_[l]) • S) := by abel
        _ = 0 := sub_eq_zero.mpr (hc.symm.trans hT)
    exact Paper5OrdinarySevenTate.rotation_not_scalar L l hl
      (scalar_of_linear_relation B S (by norm_num : (2 : ℤ_[l]) ≠ 0) hRel)
  have hFour : (4 : ℤ_[l]) • T = (4 : Module.End ℤ_[l] (Tate l (Points L))) * T := by
    rw [Algebra.smul_def, map_ofNat]
  have hSeven : (7 : ℤ_[l]) • I = (7 : Module.End ℤ_[l] (Tate l (Points L))) := by
    change (7 : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (Points L))) = _
    rw [← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have hQuad : T ^ 2 - (-4 : ℤ_[l]) • T + (7 : ℤ_[l]) • I = 0 := by
    rw [neg_smul, sub_neg_eq_add, hFour, hSeven]
    simpa only [map_add, map_mul, map_pow, map_ofNat, map_zero] using
      congrArg (endMap l) (point_quad L)
  exact trace_det_of_quadratic B T hN (-4) 7 hQuad

/-- The actual native Tate coefficients agree with the printed signed count at seven. -/
theorem trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric L)) (action L l) = -4 ∧
      LinearMap.det (action L l) = 7 := by
  rw [← tate_conjugacy]
  obtain ⟨ht, hd⟩ := ref_trace_det L l hl
  exact ⟨(LinearMap.trace_conj' _ _).trans ht, (LinearMap.det_conj _ _).trans hd⟩

theorem charpoly (hl : l = 2 ∨ l = 3) :
    letI := Module.Free.of_basis (tateBasis L l hl)
    letI := Module.Finite.of_basis (tateBasis L l hl)
    (action L l).charpoly = X ^ 2 + C (4 : ℤ_[l]) * X + C (7 : ℤ_[l]) := by
  let B := tateBasis L l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl
  change (action L l).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B,
    ht, hd, map_neg, neg_mul, sub_neg_eq_add]

end
end ManuscriptAudit.Paper5OrdinarySevenOneTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenOneTate.native_quadratic,
      ``ManuscriptAudit.Paper5OrdinarySevenOneTate.tate_quadratic,
      ``ManuscriptAudit.Paper5OrdinarySevenOneTate.tateBasis,
      ``ManuscriptAudit.Paper5OrdinarySevenOneTate.trace_det,
      ``ManuscriptAudit.Paper5OrdinarySevenOneTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
