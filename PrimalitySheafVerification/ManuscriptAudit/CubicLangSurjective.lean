import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CofiniteAdditiveRange
import PrimalitySheafVerification.ManuscriptAudit.CubicAbscissaFibers
import PrimalitySheafVerification.ManuscriptAudit.CubicLangAbscissa

/-! Surjectivity of the actual additive Frobenius-minus-identity map on the centered cubic. -/

namespace ManuscriptAudit.CubicLangSurjective

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicFrobeniusSecantPoints CubicLangAbscissa CubicAbscissaFibers
open CubicThreeTorsionCard

noncomputable section
open scoped Classical

variable (K L : Type*) [Field K] [Fintype K] [Field L] [DecidableEq L] [Algebra K L]
  [IsAlgClosed L]

/-- The native relative Frobenius minus the identity. -/
def lang (A : K) : AddMonoid.End (GeometricPoints K L A) :=
  arithmeticPointFrobenius K L A - 1

private theorem lang_apply (A : K) (P : GeometricPoints K L A) :
    lang K L A P = arithmeticPointFrobenius K L A P - P := rfl

/-- Every actual affine point away from the finite exceptional abscissas is in the image. -/
theorem affine_mem_range {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    {A : K} (hΔ : (shortCubic (0 : L) (algebraMap K L A)).Δ ≠ 0)
    {u v : L} (hR : (Curve (algebraMap K L A)).Nonsingular u v)
    (hu : u ∉ badTargets K L k A) :
    (Affine.Point.some u v hR : GeometricPoints K L A) ∈ Set.range (lang K L A) := by
  obtain ⟨x, hx, hValue⟩ := exists_secant_abscissa K L hq hk A hu
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + algebraMap K L A) (n := 2) (by decide)
  let hP := (nonsingular_iff hΔ x y).mpr hy
  let P : GeometricPoints K L A := Affine.Point.some x y hP
  have hRep := (secant_xRep K L hq A x y hP hy hx).2
  change (lang K L A P).xRep = _ at hRep
  rw [hValue] at hRep
  cases hD : lang K L A P with
  | zero =>
    have h : (0 : L) = 1 := by
      have he := congrFun hRep (1 : Fin 2)
      rw [hD] at he
      exact he
    exact (zero_ne_one h).elim
  | some s t hst =>
    have hs : s = u := by
      have he := congrFun hRep (0 : Fin 2)
      rw [hD] at he
      exact he
    subst s
    rcases same_abscissa_eq_or_neg hΔ hR hst with he | he
    · exact ⟨P, hD.trans he⟩
    · refine ⟨-P, ?_⟩
      rw [map_neg, hD, he, neg_neg]

/-- The complement of the actual image is a finite set of geometric points. -/
theorem finite_complement_range {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    {A : K} (hΔ : (shortCubic (0 : L) (algebraMap K L A)).Δ ≠ 0) :
    ((Set.range (lang K L A))ᶜ).Finite := by
  let S := badTargets K L k A
  let P := pointWithX hΔ
  have hS : (↑S : Set L).Finite := S.finite_toSet
  have hFin : ((P '' (↑S : Set L)) ∪ ((fun x => -P x) '' (↑S : Set L))).Finite :=
    (hS.image P).union (hS.image fun x => -P x)
  apply hFin.subset
  intro R hR
  cases R with
  | zero =>
    have hZero : (0 : GeometricPoints K L A) ∈ Set.range (lang K L A) :=
      ⟨0, map_zero _⟩
    exact (hR hZero).elim
  | some u v hxy =>
    have hu : u ∈ S := by
      by_contra h
      exact hR (affine_mem_range K L hq hk hΔ hxy h)
    obtain ⟨z, hz, hP⟩ := pointWithX_spec hΔ u
    rcases same_abscissa_eq_or_neg hΔ hz hxy with he | he
    · exact Or.inl ⟨u, hu, hP.trans he.symm⟩
    · exact Or.inr ⟨u, hu, (congrArg Neg.neg hP).trans he.symm⟩

/-- Lang surjectivity for the actual additive centered cubic over every good finite field. -/
theorem surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2)
    {A : K} (hA : A ≠ 0) : Function.Surjective (lang K L A) := by
  have hOdd := FiniteField.odd_card_of_char_ne_two hchar
  let k := Fintype.card K / 2
  have hq : Fintype.card K = 2 * k + 1 := by dsimp only [k]; omega
  have hk : 0 < k := Nat.div_pos Fintype.one_lt_card two_pos
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hΔ := shortCubic_discriminant_ne_zero h₂' h₃'
    ((map_ne_zero (algebraMap K L)).mpr hA)
  haveI : Infinite (GeometricPoints K L A) := infinite_points hΔ
  exact CofiniteAdditiveRange.surjective_of_finite_complement (lang K L A)
    (finite_complement_range K L hq hk hΔ)

end

end ManuscriptAudit.CubicLangSurjective

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicLangSurjective.affine_mem_range,
      ``ManuscriptAudit.CubicLangSurjective.finite_complement_range,
      ``ManuscriptAudit.CubicLangSurjective.surjective] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
