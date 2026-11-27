import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitAllPrimeTateRank
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularTwistFrobenius

/-! A sextic geometric scale transports the full native torsion tower to every ordinary finite-field twist. -/

namespace ManuscriptAudit.CubicOrdinaryAllPrimeTateRank

open Module FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace CubicPointScaling CubicSplitAllInertTate
open PowerTorsionTower TorsionFrobeniusModule PowerTateModule PowerTateRankTwo
open Paper5NonsplitFrobeniusModFour
open scoped Padic

noncomputable section
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (E L : Type) [Field E] [Field L] [IsAlgClosed L]
  [DecidableEq L] [Algebra (ZMod p) L] [Algebra E L]

/-- The native geometric curve is isomorphic to the prime-field unit-twist group after a sixth-root scale. -/
def geometricEquiv (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) :
    GeometricPoints (ZMod p) L 1 ≃+ GeometricPoints E L A := by
  let hsmall := small_char p (ZMod p) hp
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr hsmall.1
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr hsmall.2
  let a := algebraMap E L A
  have ha : a ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  let hv := IsAlgClosed.exists_pow_nat_eq a (n := 6) (by decide)
  let u := Classical.choose hv
  have hu : u ^ 6 = a := Classical.choose_spec hv
  have hu₀ : u ≠ 0 := by
    intro he
    exact ha (by simpa [he] using hu.symm)
  have hUA : u ^ 6 * (1 : L) = a := by simpa only [mul_one] using hu
  let e₀ := CubicSplitPrimeFixedCounts.transport
    (congrArg Curve (map_one (algebraMap (ZMod p) L)))
  let e := scaleEquiv hu₀ hUA
    (shortCubic_discriminant_ne_zero h₂ h₃ (one_ne_zero : (1 : L) ≠ 0))
    (shortCubic_discriminant_ne_zero h₂ h₃ ha)
  exact e₀.trans e

private def torsionEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (m : ℕ) :
    Torsion m G ≃ Torsion m H where
  toFun := mapAdd m e.toAddMonoidHom
  invFun := mapAdd m e.symm.toAddMonoidHom
  left_inv P := Subtype.ext (e.symm_apply_apply P.val)
  right_inv P := Subtype.ext (e.apply_symm_apply P.val)

variable (l : ℕ) [Fact l.Prime]

/-- Every nonzero twist over an ordinary finite extension has the square-order native torsion tower. -/
theorem card_and_scalar_surjective (hp : 5 ≤ p) (hs : p % 3 = 1) {A : E} (hA : A ≠ 0)
    (hl : p ≠ l) :
    (∀ n, Nat.card (PowerTorsion l (GeometricPoints E L A) n) = (l ^ 2) ^ n) ∧
      Function.Surjective (fun P : GeometricPoints E L A => l • P) := by
  let c := reference p L hp hs (one_ne_zero : (1 : ZMod p) ≠ 0)
  let e := geometricEquiv p E L hp hA
  have hPrime : l.Prime := Fact.out
  have hpPrime : p.Prime := Fact.out
  have hC := (Nat.coprime_primes hpPrime hPrime).mpr hl
  have hG := CubicSplitScalarSurjectivity.scalar_surjective_of_reference c hPrime.ne_zero hC
  obtain ⟨hCard, _⟩ := CubicSplitAllPrimeTateRank.card_and_transition c l hl
  refine ⟨fun n => (Nat.card_congr (torsionEquiv e (l ^ n))).symm.trans (hCard n), ?_⟩
  intro P
  obtain ⟨Q, hQ⟩ := hG (e.symm P)
  refine ⟨e Q, ?_⟩
  change l • e Q = P
  have hMul : l • Q = e.symm P := hQ
  calc
    l • e Q = e (l • Q) := (map_nsmul e l Q).symm
    _ = P := by rw [hMul, e.apply_symm_apply]

/-- The genuine native Tate module has rank two for every coefficient prime different from p. -/
def basis (hp : 5 ≤ p) (hs : p % 3 = 1) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints E L A)) :=
  (CubicSplitAllPrimeTateRank.nativeBasis (L := L) hp hs (one_ne_zero : (1 : ZMod p) ≠ 0)
    l hl).map (mapAddEquiv l (geometricEquiv p E L hp hA))

end

end ManuscriptAudit.CubicOrdinaryAllPrimeTateRank

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicOrdinaryAllPrimeTateRank.geometricEquiv,
      ``ManuscriptAudit.CubicOrdinaryAllPrimeTateRank.card_and_scalar_surjective,
      ``ManuscriptAudit.CubicOrdinaryAllPrimeTateRank.basis] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
