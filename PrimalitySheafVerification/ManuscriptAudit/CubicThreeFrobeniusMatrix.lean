import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusSigns

/-! Trace and determinant computed in the native horizontal and vertical flex basis. -/

namespace ManuscriptAudit.CubicThreeFrobeniusMatrix

open WeierstrassCurve CubicThreeTorsionBasis CubicThreeTorsionOrdinate
open CubicThreeFrobeniusSigns TorsionFrobeniusModule

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {K : Type*} [Field K] [DecidableEq K] {A : K}

private theorem signed_injective {x : K} (h₂ : (2 : K) ≠ 0) (hx : x ≠ 0) :
    Function.Injective (fun s => signed s x) := by
  have hOpp : x ≠ -x := by
    intro h
    apply mul_ne_zero h₂ hx
    calc
      (2 : K) * x = x + x := two_mul x
      _ = (-x) + x := congrArg (fun y => y + x) h
      _ = 0 := neg_add_cancel x
  intro s t h
  cases s <;> cases t
  · rfl
  · exact (hOpp (by simpa [signed] using h.symm)).elim
  · exact (hOpp (by simpa [signed] using h)).elim
  · rfl

private theorem eq_of_coordinates {P Q : (Curve A).Point}
    (hx : abscissa P = abscissa Q) (hy : ordinate P = ordinate Q)
    (h : ordinate P ≠ 0) : P = Q := by
  cases P with
  | zero => exact (h rfl).elim
  | some x y hxy =>
    cases Q with
    | zero => exact (h hy).elim
    | some a b hab =>
      simpa only [Affine.Point.some.injEq] using And.intro (show x = a from hx) (show y = b from hy)

private theorem exists_sign (σ : K →+* K) {x : K}
    (h : (σ x) ^ 2 = x ^ 2) : ∃ s : Bool, σ x = signed s x := by
  rcases ordinate_eq_of_two_squares h with hPos | hNeg
  · exact ⟨true, by simpa [signed] using hPos⟩
  · exact ⟨false, by simpa [signed] using hNeg⟩

variable (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (D : FlexPair A)
variable (σ : K →+* K) (F : Module.End (ZMod 3) (T₃ A))

private theorem matrix_signs [IsAlgClosed K]
    (hxMap : ∀ P : T₃ A, abscissa (inclusion 3 _ (F P)) = σ (abscissa (inclusion 3 _ P)))
    (hyMap : ∀ P : T₃ A, ordinate (inclusion 3 _ (F P)) = σ (ordinate (inclusion 3 _ P)))
    {s t : Bool} (hs : σ D.a = signed s D.a) (ht : σ D.b = signed t D.b) :
    LinearMap.trace (ZMod 3) (T₃ A) F = signScalar t + signScalar s ∧
      LinearMap.det F = signScalar t * signScalar s := by
  let B := basis h₂ h₃ hA D
  let U := horizontal h₂ h₃ hA D
  let T := vertical h₂ h₃ hA D
  let M := LinearMap.toMatrix B B F
  have ha : D.a ≠ 0 := by
    intro h
    exact hA (by simpa [h] using D.a_square.symm)
  have hb : D.b ≠ 0 := ordinate_nonzero_of_horizontal h₃ hA D.b_square
  have hFT : F T = signScalar s • T := by
    apply inclusion_injective 3 (Curve A).Point
    apply eq_of_coordinates
    · rw [hxMap, abscissa_smul_vertical]
      change σ (abscissa (inclusion 3 _ (vertical h₂ h₃ hA D))) = 0
      rw [abscissa_vertical, map_zero]
    · rw [hyMap]
      change σ (ordinate (inclusion 3 _ (vertical h₂ h₃ hA D))) = _
      rw [ordinate_vertical, hs]
      cases s with
      | false =>
        change -D.a = ordinate (inclusion 3 _ ((-1 : ZMod 3) • T))
        rw [neg_one_smul, map_neg, ordinate_neg]
        exact congrArg Neg.neg (ordinate_vertical h₂ h₃ hA D).symm
      | true =>
        change D.a = ordinate (inclusion 3 _ ((1 : ZMod 3) • T))
        rw [one_smul]
        exact (ordinate_vertical h₂ h₃ hA D).symm
    · rw [hyMap]
      change σ (ordinate (inclusion 3 _ (vertical h₂ h₃ hA D))) ≠ 0
      rw [ordinate_vertical]
      exact (map_ne_zero σ).mpr ha
  have hColumn (i : Fin 2) : F (B i) = M 0 i • U + M 1 i • T := by
    conv_lhs => rw [← B.sum_repr (F (B i))]
    simp [M, LinearMap.toMatrix_apply, Fin.sum_univ_two, B, U, T]
  have hU : B 0 = U := basis_zero h₂ h₃ hA D
  have hT : B 1 = T := basis_one h₂ h₃ hA D
  have h01 : M 0 1 = 0 := by
    change LinearMap.toMatrix B B F 0 1 = _
    rw [LinearMap.toMatrix_apply, hT, hFT, ← hT]
    simp
  have h11 : M 1 1 = signScalar s := by
    change LinearMap.toMatrix B B F 1 1 = _
    rw [LinearMap.toMatrix_apply, hT, hFT, ← hT]
    simp
  have h00ne : M 0 0 ≠ 0 := by
    intro h
    have hh : σ D.x = 0 := by
      calc
        _ = abscissa (inclusion 3 _ (F (B 0))) := by simp only [hxMap, hU, U, abscissa_horizontal]
        _ = _ := by rw [hColumn 0, h, zero_smul, zero_add, abscissa_smul_vertical]
    exact (map_ne_zero σ).mpr D.x_ne hh
  have hOrd : (if M 0 0 = 1 then D.b else -D.b) = signed t D.b := by
    calc
      _ = ordinate (inclusion 3 _ (M 0 0 • U + M 1 0 • T)) :=
        (ordinate_nonvertical_sum h₂ h₃ hA D _ _ h00ne).symm
      _ = ordinate (inclusion 3 _ (F (B 0))) :=
        congrArg (fun v : T₃ A => ordinate (inclusion 3 _ v)) (hColumn 0).symm
      _ = _ := by
        rw [hyMap, hU]
        change σ (ordinate (inclusion 3 _ (horizontal h₂ h₃ hA D))) = _
        rw [ordinate_horizontal]
        exact ht
  have h00 : M 0 0 = signScalar t := by
    rcases scalar_cases (M 0 0) with h | h | h
    · exact (h00ne h).elim
    · have ht' : true = t := signed_injective h₂ hb (by simpa [h, signed] using hOrd)
      simpa [← ht', signScalar] using h
    · have hneg : (-1 : ZMod 3) ≠ 1 := by decide
      have ht' : false = t := signed_injective h₂ hb (by simpa [h, hneg, signed] using hOrd)
      simpa [← ht', signScalar] using h
  constructor
  · rw [LinearMap.trace_eq_matrix_trace (ZMod 3) B]
    change M.trace = _
    rw [Matrix.trace_fin_two, h00, h11]
  · rw [← LinearMap.det_toMatrix B]
    change M.det = _
    rw [Matrix.det_fin_two, h00, h11, h01, zero_mul, sub_zero]

/-- An actual q-power map has determinant q and trace determined by its vertical sign. -/
theorem trace_det_of_coordinates [IsAlgClosed K] (q : ℕ) (hq : q % 3 ≠ 0)
    (hσ : ∀ x : K, σ x = x ^ q) (hσA : σ A = A)
    (hxMap : ∀ P : T₃ A, abscissa (inclusion 3 _ (F P)) = σ (abscissa (inclusion 3 _ P)))
    (hyMap : ∀ P : T₃ A, ordinate (inclusion 3 _ (F P)) = σ (ordinate (inclusion 3 _ P))) :
    ∃ s : Bool, σ D.a = signed s D.a ∧
      LinearMap.det F = (q : ZMod 3) ∧
      LinearMap.trace (ZMod 3) (T₃ A) F = if q % 3 = 1 then -signScalar s else 0 := by
  obtain ⟨s, hs⟩ := exists_sign σ (show (σ D.a) ^ 2 = D.a ^ 2 by
    rw [← map_pow, D.a_square, hσA])
  obtain ⟨t, ht⟩ := exists_sign σ (show (σ D.b) ^ 2 = D.b ^ 2 by
    rw [← map_pow, D.b_square]
    simp [hσA])
  obtain ⟨hTr, hDet⟩ := matrix_signs h₂ h₃ hA D σ F hxMap hyMap hs ht
  let r := D.a * D.b / A
  have hr : r ^ 2 = -(3 : K) := by
    change (D.a * D.b / A) ^ 2 = _
    rw [div_pow, mul_pow]
    apply (div_eq_iff (pow_ne_zero _ hA)).mpr
    rw [D.a_square, D.b_square]
    ring
  have hr₀ : r ≠ 0 := by
    intro h
    exact neg_ne_zero.mpr h₃ (by simpa [h] using hr.symm)
  have hmap₁ : σ r = signed (s == t) r := by
    change σ (D.a * D.b / A) = _
    rw [map_div₀, map_mul, hσA, hs, ht, signed_mul, signed_div]
  have hmap₂ := map_sqrt_neg_three q σ hσ hq h₂ hr
  have hsame : (s == t) = decide (q % 3 = 1) :=
    signed_injective h₂ hr₀ (hmap₁.symm.trans hmap₂)
  have hqCast : signScalar (decide (q % 3 = 1)) = (q : ZMod 3) := by
    rw [← ZMod.natCast_mod q 3]
    by_cases hq₁ : q % 3 = 1
    · simp [hq₁, signScalar]
    · have hq₂ : q % 3 = 2 := by omega
      simpa [hq₁, hq₂, signScalar] using (show (-1 : ZMod 3) = 2 by decide)
  refine ⟨s, hs, ?_, ?_⟩
  · rw [hDet, mul_comm, signScalar_mul, hsame, hqCast]
  · by_cases hq₁ : q % 3 = 1
    · have hst : s = t := by cases s <;> cases t <;> simp_all
      rw [hTr, if_pos hq₁, hst, signScalar_add_self]
    · have hst : s ≠ t := by intro he; subst t; simp [hq₁] at hsame
      rw [hTr, if_neg hq₁]
      exact signScalar_add_of_ne hst.symm

end
end ManuscriptAudit.CubicThreeFrobeniusMatrix

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CubicThreeFrobeniusMatrix.trace_det_of_coordinates
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
