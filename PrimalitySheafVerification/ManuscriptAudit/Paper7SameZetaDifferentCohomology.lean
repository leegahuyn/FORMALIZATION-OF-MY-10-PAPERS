import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportCyclicDegrees
import PrimalitySheafVerification.ManuscriptAudit.CuspSchemePointCounts
import PrimalitySheafVerification.ManuscriptAudit.NodalSchemeHasseWeil
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothEulerComparison

/-! Equal native point-count zeta functions can have different degree-one compact cohomology. -/

namespace ManuscriptAudit.Paper7SameZetaDifferentCohomology

open CategoryTheory PowerSeries
open CuspHasseWeilSeries CuspPointCountSeries CuspCompactSupportSequence
open SchemeRationalPointsOpen NodalSmoothEulerComparison

noncomputable section

def nativeCuspCounts (p : ℕ) [Fact p.Prime] : Series :=
  X * PowerSeries.mk fun n =>
    (Nat.card (PointsOver
      (CuspProperCompactification.affineOpen (GaloisField p (n + 1)) ≫
        CuspProperCompactification.projectiveCuspToBase (GaloisField p (n + 1)))) : ℚ)

theorem nativeCuspCounts_eq (p : ℕ) [Fact p.Prime] :
    nativeCuspCounts p = cuspSeries p := by
  unfold nativeCuspCounts cuspSeries
  congr 1
  ext n
  simp only [PowerSeries.coeff_mk]
  exact congrArg (fun m : ℕ => (m : ℚ))
    ((CuspSchemePointCounts.affine_card (GaloisField p (n + 1))).trans
      (CuspPointCounts.curve_card (GaloisField p (n + 1))).symm)

theorem equal_zeta (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    zetaOfCountSeries (NodalSchemeHasseWeil.properCounts p) =
      zetaOfCountSeries (nativeCuspCounts p) := by
  rw [nativeCuspCounts_eq, NodalSchemeHasseWeil.proper_zeta_eq p hp₂, ← cuspZeta_eq_inv p] <;> rfl

variable (K : Type) [Field K] [IsAlgClosed K]

theorem same_zeta_distinct_compact_degree_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp₂ : p ≠ 2) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    zetaOfCountSeries (NodalSchemeHasseWeil.properCounts p) =
      zetaOfCountSeries (nativeCuspCounts p) ∧
      properCompactBetti K ℓ 1 = 1 ∧
      Subsingleton (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 1) := by
  have h₂ : (2 : K) ≠ 0 := by
    intro h
    have hc : ((2 : ℕ) : K) = 0 := by simpa using h
    have hd := (CharP.cast_eq_zero_iff K p 2).mp hc
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp₂ h
  have he := CuspCompactSupportCyclicDegrees.cuspEquiv K p ℓ (Fact.out : ℓ.Prime).two_le 1
  have e : cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 1 ≃+ ZMod 1 := by
    simpa only [show (1 : ℕ) ≠ 2 by decide, if_false] using he
  exact ⟨equal_zeta p hp₂, (proper_compact_betti_eq K ℓ 1).trans
    ((proper_betti_succ K ℓ 0).trans (NodalFiniteCohomology.betti_one K ℓ h₂)),
    e.injective.subsingleton⟩

end
end ManuscriptAudit.Paper7SameZetaDifferentCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7SameZetaDifferentCohomology.nativeCuspCounts_eq,
      ``ManuscriptAudit.Paper7SameZetaDifferentCohomology.equal_zeta,
      ``ManuscriptAudit.Paper7SameZetaDifferentCohomology.same_zeta_distinct_compact_degree_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
