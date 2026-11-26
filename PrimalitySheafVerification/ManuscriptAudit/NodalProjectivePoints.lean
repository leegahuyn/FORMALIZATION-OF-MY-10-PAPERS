import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Basic
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePointCounts

/-! Actual homogeneous point classes and smooth points of the projective node. -/

namespace ManuscriptAudit.NodalProjectivePoints

open WeierstrassCurve WeierstrassCurve.Projective NodalAffinePointCounts
open scoped Matrix

noncomputable section

variable (K : Type*) [Field K]

def model : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 0, a₆ := 0 }

abbrev projectivePoints :=
  {q : PointClass K // ∃ P : Fin 3 → K, P ≠ 0 ∧ (model K).toProjective.Equation P ∧
    (⟦P⟧ : PointClass K) = q}

private theorem affine_equation (a b : K) :
    (model K).toAffine.Equation a b ↔ b ^ 2 = a ^ 2 * (a + 1) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [model, WeierstrassCurve.toAffine] <;> ring_nf

private def toProjective : Option (affinePoints K) → projectivePoints K
  | none => ⟨⟦![0, 1, 0]⟧, ![0, 1, 0],
      fun h => one_ne_zero (congrFun h 1), equation_zero, rfl⟩
  | some q => ⟨⟦![q.val.1, q.val.2, 1]⟧, ![q.val.1, q.val.2, 1],
      fun h => one_ne_zero (congrFun h 2), (equation_some _ _).mpr
        ((affine_equation K _ _).mpr q.property), rfl⟩

private theorem toProjective_injective : Function.Injective (toProjective K) := by
  intro p q e
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some q =>
      have h : (![0, 1, 0] : Fin 3 → K) ≈ ![q.val.1, q.val.2, 1] :=
        Quotient.eq.mp (congrArg Subtype.val e)
      exfalso
      exact not_equiv_of_Z_eq_zero_left rfl one_ne_zero h
  | some p =>
    cases q with
    | none =>
      have h : (![p.val.1, p.val.2, 1] : Fin 3 → K) ≈ ![0, 1, 0] :=
        Quotient.eq.mp (congrArg Subtype.val e)
      exfalso
      exact not_equiv_of_Z_eq_zero_right one_ne_zero rfl h
    | some q =>
      have h : (![p.val.1, p.val.2, 1] : Fin 3 → K) ≈ ![q.val.1, q.val.2, 1] :=
        Quotient.eq.mp (congrArg Subtype.val e)
      have h₁ : p.val.1 = q.val.1 := by simpa using X_eq_of_equiv h
      have h₂ : p.val.2 = q.val.2 := by simpa using Y_eq_of_equiv h
      exact congrArg some (Subtype.ext (Prod.ext h₁ h₂))

private theorem toProjective_surjective : Function.Surjective (toProjective K) := by
  classical
  rintro ⟨q, P, hP, he, rfl⟩
  by_cases hz : P 2 = 0
  · have hx := X_eq_zero_of_Z_eq_zero he hz
    have hy : P 1 ≠ 0 := by
      intro h
      apply hP
      rw [← fin3_def P]
      ext i
      fin_cases i
      · exact hx
      · exact h
      · exact hz
    have hs : (P 1) • (![0, 1, 0] : Fin 3 → K) = P := by
      calc
        _ = ![0, P 1, 0] := by simp [smul_fin3]
        _ = P := by
          simpa only [hx, hz] using fin3_def P
    have hrel : P ≈ (![0, 1, 0] : Fin 3 → K) := by
      rw [← hs]
      exact smul_equiv _ (isUnit_iff_ne_zero.mpr hy)
    exact ⟨none, Subtype.ext (Quotient.eq.mpr (Setoid.symm hrel))⟩
  · have hrel := equiv_some_of_Z_ne_zero hz
    have ha := (equation_some (P 0 / P 2) (P 1 / P 2)).mp
      ((equation_of_equiv hrel).mp he)
    exact ⟨some ⟨(P 0 / P 2, P 1 / P 2), (affine_equation K _ _).mp ha⟩,
      Subtype.ext (Quotient.eq.mpr (Setoid.symm hrel))⟩

/-- The projective points are the full affine nodal chart and the unique point at infinity. -/
def projectiveEquiv : Option (affinePoints K) ≃ projectivePoints K :=
  Equiv.ofBijective (toProjective K) ⟨toProjective_injective K, toProjective_surjective K⟩

private theorem affine_nonsingular_iff (h2 : (2 : K) ≠ 0) (a b : K) :
    (model K).toAffine.Nonsingular a b ↔ b ^ 2 = a ^ 2 * (a + 1) ∧ a ≠ 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, affine_equation K]
  constructor
  · rintro ⟨he, hh⟩
    refine ⟨he, ?_⟩
    intro e
    subst a
    have hb : b * b = 0 := by simpa [pow_two] using he
    have hb₀ := (mul_eq_zero.mp hb).elim id id
    subst b
    simpa [model, WeierstrassCurve.toAffine] using hh
  · rintro ⟨he, ha⟩
    refine ⟨he, ?_⟩
    simp only [model, WeierstrassCurve.toAffine, zero_mul, one_mul, mul_one, add_zero, sub_zero]
    by_cases hb : b = 0
    · left
      have h₁ : a + 1 = 0 := by
        have he' : a ^ 2 * (a + 1) = 0 := by simpa [hb] using he.symm
        exact (mul_eq_zero.mp he').resolve_left (pow_ne_zero _ ha)
      have h_a : a = -1 := by
        calc
          a = a + 1 - 1 := (add_sub_cancel_right a 1).symm
          _ = -1 := by rw [h₁, zero_sub]
      rw [h_a]
      norm_num
    · right
      intro h
      have hz : (2 : K) * b = 0 := by linear_combination h
      exact (mul_ne_zero h2 hb) hz

/-- Mathlib's nonsingular projective points are the smooth affine points plus infinity. -/
def smoothEquiv (h2 : (2 : K) ≠ 0) :
    (model K).toProjective.Point ≃ Option (smoothAffine K) := by
  classical
  let e : {xy : K × K // (model K).toAffine.Nonsingular xy.1 xy.2} ≃
      smoothAffine K :=
    { toFun := fun q =>
        let h := (affine_nonsingular_iff K h2 _ _).mp q.property
        ⟨⟨q.val, h.1⟩, h.2⟩
      invFun := fun q => ⟨q.val.val,
        (affine_nonsingular_iff K h2 _ _).mpr ⟨q.val.property, q.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ((WeierstrassCurve.Projective.Point.toAffineAddEquiv (model K).toProjective).toEquiv.trans
    (model K).toAffine.nonsingularPointEquiv).trans (Equiv.optionCongr e)

theorem projective_point_counts [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (projectivePoints K) = Nat.card K ∧
    Nat.card (model K).toProjective.Point + 1 = Nat.card K := by
  classical
  letI : Fintype (affinePoints K) := Fintype.ofFinite _
  letI : Fintype (smoothAffine K) := Fintype.ofFinite _
  letI : Fintype (projectivePoints K) := Fintype.ofEquiv _ (projectiveEquiv K)
  letI : Fintype (model K).toProjective.Point := Fintype.ofEquiv _ (smoothEquiv K h2).symm
  obtain ⟨hs, ha⟩ := affine_point_counts K h2
  have hp := Fintype.card_congr (projectiveEquiv K)
  have hV := Fintype.card_congr (smoothEquiv K h2)
  rw [Fintype.card_option] at hp hV
  simp only [← Nat.card_eq_fintype_card] at hp hV
  omega

/-- The split nodal cubic and its smooth locus over every odd finite extension. -/
theorem prime_power_point_counts (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (hp₂ : p ≠ 2) :
    Nat.card (projectivePoints (GaloisField p n)) = p ^ n ∧
    Nat.card (model (GaloisField p n)).toProjective.Point + 1 = p ^ n := by
  have h₂ : (2 : GaloisField p n) ≠ 0 := by
    intro e
    have hcast : ((2 : ℕ) : GaloisField p n) = 0 := by simpa using e
    have hd := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).mp hcast
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp₂ h
  simpa only [GaloisField.card p (n := n) hn] using
    projective_point_counts (GaloisField p n) h₂

end
end ManuscriptAudit.NodalProjectivePoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectivePoints.projectiveEquiv,
      ``ManuscriptAudit.NodalProjectivePoints.smoothEquiv,
      ``ManuscriptAudit.NodalProjectivePoints.projective_point_counts,
      ``ManuscriptAudit.NodalProjectivePoints.prime_power_point_counts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
