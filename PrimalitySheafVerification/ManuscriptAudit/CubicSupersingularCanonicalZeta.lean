import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.GaloisField
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularHasseWeil

/-! Real relative finite fields for the actual zeta series, constructed in every positive degree. -/

namespace ManuscriptAudit.CubicSupersingularCanonicalZeta

open Module PowerSeries PointCountExponential CubicSupersingularPointCountRecurrence

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [Algebra (ZMod p) F] [CharP F p]

abbrev Extension (n : ℕ) := GaloisField p (finrank (ZMod p) F * (n + 1))

private theorem baseRank_pos : 0 < finrank (ZMod p) F := Module.finrank_pos

private theorem absoluteRank_extension (n : ℕ) :
    finrank (ZMod p) (Extension p F n) = finrank (ZMod p) F * (n + 1) :=
  GaloisField.finrank p (Nat.mul_ne_zero (ne_of_gt (baseRank_pos p F)) (Nat.succ_ne_zero n))

private def baseEmbedding (n : ℕ) : F →ₐ[ZMod p] Extension p F n :=
  Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := F) (L := Extension p F n) (by
      rw [absoluteRank_extension p F n]
      exact dvd_mul_right _ _))

noncomputable local instance extensionAlgebra (n : ℕ) : Algebra F (Extension p F n) :=
  (baseEmbedding p F n).toRingHom.toAlgebra

local instance extensionScalarTower (n : ℕ) : IsScalarTower (ZMod p) F (Extension p F n) :=
  IsScalarTower.of_algebraMap_eq fun r => ((baseEmbedding p F n).commutes r).symm

theorem relativeRank (n : ℕ) :
    finrank F (Extension p F n) = n + 1 := by
  apply mul_left_cancel₀ (ne_of_gt (baseRank_pos p F))
  exact (Module.finrank_mul_finrank (ZMod p) F (Extension p F n)).trans
    (absoluteRank_extension p F n)

abbrev Closure := AlgebraicClosure F

private def closureEmbedding (n : ℕ) : Extension p F n →ₐ[F] Closure F :=
  IsAlgClosed.lift (R := F) (S := Extension p F n) (M := Closure F)

noncomputable local instance intoClosure (n : ℕ) : Algebra (Extension p F n) (Closure F) :=
  (closureEmbedding p F n).toRingHom.toAlgebra

local instance closureScalarTower (n : ℕ) : IsScalarTower F (Extension p F n) (Closure F) :=
  IsScalarTower.of_algebraMap_eq fun r => ((closureEmbedding p F n).commutes r).symm

noncomputable local instance finiteExtension (n : ℕ) : Fintype (Extension p F n) :=
  Fintype.ofFinite _

noncomputable local instance decEqExtension (n : ℕ) : DecidableEq (Extension p F n) :=
  Classical.decEq _

variable [DecidableEq F]

/-- This count series uses genuine finite fields with the required relative degrees. -/
def actualCounts (A : F) : ℂ⟦X⟧ :=
  CubicSupersingularHasseWeil.counts F (Extension p F) A

theorem zeta_eq (hp : 5 ≤ p) (hP : p % 3 = 2) {A : F} (hA : A ≠ 0) :
    zetaOfCountSeries (actualCounts p F A) =
      (1 - X * C (signedCount F A : ℂ) + X ^ 2 * C (Fintype.card F : ℂ)) *
        ((1 - X)⁻¹ * (1 - X * C (Fintype.card F : ℂ))⁻¹) := by
  classical
  letI : Algebra.IsAlgebraic (ZMod p) (Closure F) :=
    Algebra.IsAlgebraic.trans (ZMod p) F (Closure F)
  exact CubicSupersingularHasseWeil.zeta_eq F (Extension p F) p (Closure F)
    hp hP (relativeRank p F) hA

end
end ManuscriptAudit.CubicSupersingularCanonicalZeta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularCanonicalZeta.relativeRank,
      ``ManuscriptAudit.CubicSupersingularCanonicalZeta.zeta_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
