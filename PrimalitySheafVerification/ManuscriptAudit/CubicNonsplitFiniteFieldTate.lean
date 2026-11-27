import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricScaling
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitAllPrimeAdic

/-! The full nonsplit Frobenius polynomial over finite extensions of a prime field. -/

namespace ManuscriptAudit.CubicNonsplitFiniteFieldTate

open Polynomial Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open PowerTateModule CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius
open CubicGeometricScaling

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

/-- Scaling transports the native rank-two Tate module to every centered twist in this characteristic. -/
def centeredBasis (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : L}
    (hA₀ : A ≠ 0) (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) :
    Basis (Fin 2) ℤ_[l] (Tate l (Curve A).Point) := by
  let a := algebraMap (ZMod p) L (1 : ZMod p)
  have ha : a ≠ 0 := (map_ne_zero (algebraMap (ZMod p) L)).mpr one_ne_zero
  obtain ⟨h₂, h₃⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃
  let e := Classical.choice (exists_scaleEquiv ha hA₀
    (shortCubic_discriminant_ne_zero h₂L h₃L ha) hΔ)
  let B : Basis (Fin 2) ℤ_[l] (Tate l (Curve a).Point) :=
    Paper5NonsplitAllPrimeAdic.actualBasis p L l hp hq hlp (A := 1) one_ne_zero
  exact B.map (mapAddEquiv l e)

variable (E : Type*) [Field E] [Fintype E] [Algebra E L] [CharP E p]

/-- Every nonsplit centered cubic over a finite field in this characteristic has native rank two. -/
def actualBasis (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints E L A)) := by
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  exact centeredBasis p L l hp hq hlp ((map_ne_zero (algebraMap E L)).mpr hA)
    (shortCubic_discriminant_ne_zero h₂L h₃L ((map_ne_zero (algebraMap E L)).mpr hA))

private theorem odd_card (hp : 5 ≤ p) : Fintype.card E % 2 = 1 := by
  apply FiniteField.odd_card_of_char_ne_two
  rw [ringChar.eq E p]
  omega

/-- The actual Frobenius determinant is the size of the finite field at every admissible prime. -/
theorem determinant (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) (hE : Fintype.card E % 3 = 2) :
    LinearMap.det (Action E L l A) = (Fintype.card E : ℤ_[l]) :=
  determinant_eq_card E L l h₂ h₃ hA hE (odd_card p E hp)
    (actualBasis p L l E hp hq hlp h₂ h₃ hA)

/-- The full native characteristic polynomial is T²+q over every coefficient prime away from p. -/
theorem charpoly (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) (hE : Fintype.card E % 3 = 2) :
    letI := Module.Free.of_basis (actualBasis p L l E hp hq hlp h₂ h₃ hA)
    letI := Module.Finite.of_basis (actualBasis p L l E hp hq hlp h₂ h₃ hA)
    (Action E L l A).charpoly = X ^ 2 + C (Fintype.card E : ℤ_[l]) :=
  charpoly_eq E L l h₂ h₃ hA hE (odd_card p E hp)
    (actualBasis p L l E hp hq hlp h₂ h₃ hA)

end
end ManuscriptAudit.CubicNonsplitFiniteFieldTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNonsplitFiniteFieldTate.centeredBasis,
      ``ManuscriptAudit.CubicNonsplitFiniteFieldTate.actualBasis,
      ``ManuscriptAudit.CubicNonsplitFiniteFieldTate.determinant,
      ``ManuscriptAudit.CubicNonsplitFiniteFieldTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
