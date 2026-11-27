import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.CubicDoublingSurjective

/-! The actual 2-adic and 3-adic characteristic polynomials, with no rank hypotheses. -/

namespace ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly

open Polynomial Module CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius
open PowerTateModule PowerTateRankTwo CubicThreeAdicTate CubicDoublingSurjective

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

local notation "q" => Fintype.card E

private theorem two_ne (h₂ : (2 : E) ≠ 0) : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂

private theorem three_ne (h₃ : (3 : E) ≠ 0) : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃

private theorem card_mod_two (h₂ : (2 : E) ≠ 0) : q % 2 = 1 := by
  apply FiniteField.odd_card_of_char_ne_two
  intro h
  have hd : ringChar E ∣ 2 := by rw [h]
  apply h₂
  simpa only [Nat.cast_ofNat] using (ringChar.spec E 2).mpr hd

def twoAdicBasis {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[2] (Tate 2 (GeometricPoints E L A)) :=
  let h₂L := two_ne E L h₂
  let h₃L := three_ne E L h₃
  let hAL := (map_ne_zero (algebraMap E L)).mpr hA
  (Basis.finTwoProd ℤ_[2]).map (padicPairEquiv 2 (GeometricPoints E L A)
    (CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L hAL 1)
    (affine_doubling_surjective h₂L h₃L hAL))

def threeAdicBasis {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[3] (Tate 3 (GeometricPoints E L A)) :=
  (Basis.finTwoProd ℤ_[3]).map
    (affinePadicCoordinates (two_ne E L h₂) (three_ne E L h₃)
      ((map_ne_zero (algebraMap E L)).mpr hA))

theorem two_adic_determinant {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq3 : q % 3 = 2) :
    LinearMap.det (Action E L 2 A) = (q : ℤ_[2]) :=
  determinant_eq_card E L 2 h₂ h₃ hA hq3 (card_mod_two E h₂) (twoAdicBasis E L h₂ h₃ hA)

theorem three_adic_determinant {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq3 : q % 3 = 2) :
    LinearMap.det (Action E L 3 A) = (q : ℤ_[3]) :=
  determinant_eq_card E L 3 h₂ h₃ hA hq3 (card_mod_two E h₂) (threeAdicBasis E L h₂ h₃ hA)

theorem two_adic_charpoly {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq3 : q % 3 = 2) :
    letI := Module.Free.of_basis (twoAdicBasis E L h₂ h₃ hA)
    letI := Module.Finite.of_basis (twoAdicBasis E L h₂ h₃ hA)
    (Action E L 2 A).charpoly = X ^ 2 + C (q : ℤ_[2]) :=
  charpoly_eq E L 2 h₂ h₃ hA hq3 (card_mod_two E h₂) (twoAdicBasis E L h₂ h₃ hA)

theorem three_adic_charpoly {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq3 : q % 3 = 2) :
    letI := Module.Free.of_basis (threeAdicBasis E L h₂ h₃ hA)
    letI := Module.Finite.of_basis (threeAdicBasis E L h₂ h₃ hA)
    (Action E L 3 A).charpoly = X ^ 2 + C (q : ℤ_[3]) :=
  charpoly_eq E L 3 h₂ h₃ hA hq3 (card_mod_two E h₂) (threeAdicBasis E L h₂ h₃ hA)

end
end ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly.twoAdicBasis,
      ``ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly.threeAdicBasis,
      ``ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly.two_adic_determinant,
      ``ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly.three_adic_determinant,
      ``ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly.two_adic_charpoly,
      ``ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly.three_adic_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
