import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicAllGoodFiniteFieldTate
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveHOnePadic

/-! Rank two for actual full small étale H¹ of each good centered cubic
over the geometric field, at every coefficient prime away from the characteristic. -/

namespace ManuscriptAudit.CubicProjectiveEtaleRank

open AlgebraicGeometry CategoryTheory Module WeierstrassCurve
open CubicNonsplitThreeAdicTrace CubicThreeTorsionOrdinate CubicThreeTorsionCard FiniteFieldPointCount
open WeierstrassProjectiveClosure WeierstrassProjectiveHOnePadic FullEtaleHOnePadic
open PowerTateModule
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E L : Type) [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod p) E] [CharP E p]
  [Field L] [DecidableEq L] [Algebra E L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

private abbrev W (a : E) := Curve (algebraMap E L a)

private theorem discriminant_isUnit (hp : 5 ≤ p) {a : E} (ha : a ≠ 0) :
    (W E L a).IsElliptic := by
  have h₂E : (2 : E) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff E p 2).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (lt_of_lt_of_le (by decide : 2 < 5) hp)) hd
  have h₃E : (3 : E) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff E p 3).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) (lt_of_lt_of_le (by decide : 3 < 5) hp)) hd
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂E
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃E
  have haL : algebraMap E L a ≠ 0 := (map_ne_zero (algebraMap E L)).mpr ha
  exact ⟨isUnit_iff_ne_zero.mpr (shortCubic_discriminant_ne_zero h₂ h₃ haL)⟩

private theorem coefficient_ne_zero (hpl : p ≠ l) : (l : L) ≠ 0 := by
  have hlE : (l : E) ≠ 0 := by
    intro h
    have hd : p ∣ l := (CharP.cast_eq_zero_iff E p l).mp h
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).mp hd with h₁ | h₂
    · exact (Fact.out : p.Prime).ne_one h₁
    · exact hpl h₂
  simpa only [map_natCast] using (map_ne_zero (algebraMap E L)).mpr hlE

/-- On the genuine twisted étale coefficient tower the p-adic module
has an integral basis of rank two. -/
def rootsBasis (hp : 5 ≤ p) {a : E} (ha : a ≠ 0) (hpl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (RootsHOne (projectiveScheme (W E L a)) l) := by
  letI : (W E L a).IsElliptic := discriminant_isUnit p E L hp ha
  letI : NeZero (l : L) := ⟨coefficient_ne_zero p E L l hpl⟩
  exact (CubicAllGoodFiniteFieldTate.basis p E L l hp ha hpl).map
    (rootsTateLinearEquiv (W E L a) l).symm

/-- On the genuine untwisted étale coefficient tower the p-adic module
has an integral basis of rank two. -/
def cyclicBasis (hp : 5 ≤ p) {a : E} (ha : a ≠ 0) (hpl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (CyclicHOne (projectiveScheme (W E L a)) l) := by
  letI : (W E L a).IsElliptic := discriminant_isUnit p E L hp ha
  letI : NeZero (l : L) := ⟨coefficient_ne_zero p E L l hpl⟩
  exact (CubicAllGoodFiniteFieldTate.basis p E L l hp ha hpl).map
    (cyclicTateLinearEquiv (W E L a) l).symm

end

end ManuscriptAudit.CubicProjectiveEtaleRank

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicProjectiveEtaleRank.rootsBasis,
      ``ManuscriptAudit.CubicProjectiveEtaleRank.cyclicBasis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
