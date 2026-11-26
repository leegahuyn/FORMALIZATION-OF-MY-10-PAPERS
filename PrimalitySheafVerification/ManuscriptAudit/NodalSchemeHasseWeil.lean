import Lean.Util.CollectAxioms
import Mathlib.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.NodalHasseWeilSeries
import PrimalitySheafVerification.ManuscriptAudit.NodalSchemePointCounts
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusOverlap

/-! Hasse–Weil series from literal rational morphisms into the proper nodal
scheme or its actual smooth locus. -/

namespace ManuscriptAudit.NodalSchemeHasseWeil

open AlgebraicGeometry CategoryTheory
open scoped PowerSeries
open SchemeRationalPointsOpen
open NodalProjectiveClosure
open NodalSmoothLocus (nodePoint smoothLocus_eq_complement)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalAffineOrigin (originMap originAlgebra originPoint)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K]

private abbrev smoothToBase := (smoothOpen K).ι ≫ projectiveNodeToBase K

private def singularRationalPoint : PointsOver (projectiveNodeToBase K) :=
  ⟨originMap K ≫ affineOpen K, by
    rw [Category.assoc, affineOpen_toBase, originMap, ← Spec.map_comp, ← Spec.map_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (originAlgebra K).commutes⟩

private def smoothOptionEquiv :
    Option (PointsOver (smoothToBase K)) ≃ PointsOver (projectiveNodeToBase K) := by
  apply SchemeRationalPointsOpen.optionEquiv (projectiveNodeToBase K) (smoothOpen K).ι
    (singularRationalPoint K)
  · rw [Scheme.Opens.range_ι, smoothLocus_eq_complement]
    exact fun h => h rfl
  · intro x
    rw [Scheme.Opens.range_ι, smoothLocus_eq_complement]
    intro h
    exact Set.mem_singleton_iff.mp (not_not.mp h)

/-- Counts of rational scheme morphisms into the actual smooth and proper loci
differ by exactly one in every finite field of odd characteristic. -/
theorem smooth_card_succ [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (PointsOver (smoothToBase K)) + 1 = Nat.card K := by
  classical
  let p := NodalSchemePointCounts.properEquiv K
  let e := smoothOptionEquiv K
  letI : Finite (PointsOver (projectiveNodeToBase K)) := Finite.of_injective p p.injective
  letI : Finite (PointsOver (smoothToBase K)) :=
    Finite.of_injective (fun a => e (some a)) (fun _ _ h => Option.some.inj (e.injective h))
  letI : Fintype (PointsOver (projectiveNodeToBase K)) := Fintype.ofFinite _
  letI : Fintype (PointsOver (smoothToBase K)) := Fintype.ofFinite _
  have h : Nat.card (PointsOver (smoothToBase K)) + 1 =
      Nat.card (PointsOver (projectiveNodeToBase K)) := by
    simpa only [Fintype.card_option, Nat.card_eq_fintype_card] using Fintype.card_congr e
  exact h.trans (NodalSchemePointCounts.proper_card K h2)

private abbrev Series := ℚ⟦X⟧

private theorem two_ne_zero_galois (p n : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    (2 : GaloisField p n) ≠ 0 := by
  intro e
  have hcast : ((2 : ℕ) : GaloisField p n) = 0 := by simpa using e
  have hd := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).mp hcast
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hp₂ h

/-- The point-count series of the actual proper scheme. -/
def properCounts (p : ℕ) [Fact p.Prime] : Series :=
  PowerSeries.X * PowerSeries.mk fun n =>
    (Nat.card (PointsOver (projectiveNodeToBase (GaloisField p (n + 1)))) : ℚ)

/-- The point-count series of the actual smooth open. -/
def smoothCounts (p : ℕ) [Fact p.Prime] : Series :=
  PowerSeries.X * PowerSeries.mk fun n =>
    (Nat.card (PointsOver (smoothToBase (GaloisField p (n + 1)))) : ℚ)

private theorem properCounts_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    properCounts p = NodalHasseWeilSeries.nodalCounts p := by
  unfold properCounts NodalHasseWeilSeries.nodalCounts
  apply congrArg (fun r : Series => (PowerSeries.X : Series) * r)
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    NodalSchemePointCounts.proper_card _ (two_ne_zero_galois p _ hp₂),
    (NodalProjectivePoints.projective_point_counts _ (two_ne_zero_galois p _ hp₂)).1]

private theorem smoothCounts_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    smoothCounts p = NodalHasseWeilSeries.smoothCounts p := by
  unfold smoothCounts NodalHasseWeilSeries.smoothCounts
  apply congrArg (fun r : Series => (PowerSeries.X : Series) * r)
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have h := smooth_card_succ (GaloisField p (n + 1)) (two_ne_zero_galois p _ hp₂)
  have h' := (NodalProjectivePoints.projective_point_counts
    (GaloisField p (n + 1)) (two_ne_zero_galois p _ hp₂)).2
  exact congrArg (fun m : ℕ => (m : ℚ)) (by omega)

/-- Exact proper Hasse–Weil factor from scheme morphisms over all finite extensions. -/
theorem proper_zeta_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    CuspHasseWeilSeries.zetaOfCountSeries (properCounts p) =
      (1 - (PowerSeries.X : Series) * PowerSeries.C (p : ℚ))⁻¹ := by
  rw [properCounts_eq p hp₂]
  exact NodalHasseWeilSeries.nodalZeta_eq p hp₂

/-- Exact smooth-open Hasse–Weil factor from the same geometric construction. -/
theorem smooth_zeta_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    CuspHasseWeilSeries.zetaOfCountSeries (smoothCounts p) =
      (1 - (PowerSeries.X : Series)) *
        (1 - (PowerSeries.X : Series) * PowerSeries.C (p : ℚ))⁻¹ := by
  rw [smoothCounts_eq p hp₂]
  exact NodalHasseWeilSeries.smoothZeta_eq p hp₂

end
end ManuscriptAudit.NodalSchemeHasseWeil

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSchemeHasseWeil.smooth_card_succ,
      ``ManuscriptAudit.NodalSchemeHasseWeil.proper_zeta_eq,
      ``ManuscriptAudit.NodalSchemeHasseWeil.smooth_zeta_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
