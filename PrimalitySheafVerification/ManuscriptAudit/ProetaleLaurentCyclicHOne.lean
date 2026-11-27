import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Ideal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerBoundaryNative
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineLineCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnitProductCoordinates

/-! Native degree-one cohomology of the Laurent line is the cyclic
group of Laurent exponents, via the actual Kummer unit boundary. -/

namespace ManuscriptAudit.ProetaleLaurentCyclicHOne

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
open ProetaleAffineLineCyclicHOne (unitsHZeroEquiv)
open ProetaleConstantRestriction (constant)
open ProetaleKummerPower (J G)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerBoundaryNative
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev R := LaurentPolynomial K
private abbrev Y := Spec (CommRingCat.of (R K))
private abbrev k : Y K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (R K)))

local instance laurentDomain : IsDomain (R K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R K)
    (show Submonoid.powers (Polynomial.X : Polynomial K) ≤ (Polynomial K)⁰ from by
      rintro _ ⟨n, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n Polynomial.X_ne_zero))

local instance laurentPID : IsPrincipalIdealRing (R K) := ⟨fun I ↦ by
  rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : Polynomial K)) (R K) I]
  exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (R K))
    (inferInstance : (I.under (Polynomial K)).IsPrincipal)⟩

private def integerCoordinate : ℤ →+ (Additive Kˣ × ℤ) where
  toFun n := (0, n)
  map_zero' := rfl
  map_add' _ _ := by simp

variable [IsAlgClosed K]

private theorem scalar_root (d : ℕ) (hd : 0 < d) (a : Additive Kˣ) : ∃ b : Additive Kˣ, d • b = a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : K) hd
  have hn : b ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hb
    exact a.toMul.ne_zero hb.symm
  refine ⟨Additive.ofMul (Units.mk0 b hn), Additive.ext (Units.ext ?_)⟩
  exact hb

set_option maxHeartbeats 1500000 in
/-- The generator 1 maps to the actual Kummer class of the Laurent coordinate. -/
def cyclicToHOne (d : ℕ) [NeZero (d : K)] :
    ZMod d ≃+ Sheaf.H (constant (Y K) (ZMod d)) 1 := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let e := (unitsHZeroEquiv (R K)).trans (LaurentUnitProductCoordinates.unitCoordinates K).symm
  let v := e.symm.toAddMonoidHom.comp (integerCoordinate K)
  let b := unitBoundary (k K) d
  let h := b.comp v
  have hv (n : ℤ) : e (v n) = (0, n) := e.apply_symm_apply _
  have hKer (n : ℤ) : h n = 0 ↔ (d : ℤ) ∣ n := by
    change unitBoundary (k K) d (v n) = 0 ↔ _
    rw [unitBoundary_eq_zero_iff]
    constructor
    · rintro ⟨c, hc⟩
      have he := congrArg e hc
      rw [map_nsmul, hv] at he
      have hn : d • (e c).2 = n := congrArg Prod.snd he
      exact ⟨(e c).2, by simpa only [nsmul_eq_mul] using hn.symm⟩
    · rintro ⟨m, rfl⟩
      refine ⟨v m, e.injective ?_⟩
      rw [map_nsmul, hv, hv]
      apply Prod.ext
      · change d • (0 : Additive Kˣ) = 0
        rw [nsmul_zero]
      · change d • m = (d : ℤ) * m
        rw [nsmul_eq_mul]
  let q := ZMod.lift d ⟨h, (hKer (d : ℤ)).mpr dvd_rfl⟩
  have hqi : Function.Injective q := by
    dsimp only [q]
    rw [ZMod.lift_injective]
    intro n hn
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n d).mpr ((hKer n).mp hn)
  have hqs : Function.Surjective q := by
    intro a
    obtain ⟨x, hx⟩ := unitBoundary_surjective (k K) d (ProetalePIDUnitHOne.HOne_subsingleton (R K)) a
    obtain ⟨y, hy⟩ := scalar_root K d hd (e x).1
    let r := (e x).2
    let z := e.symm (y, 0)
    have hz : unitBoundary (k K) d (d • z) = 0 :=
      (unitBoundary_eq_zero_iff (k K) d (d • z)).mpr ⟨z, rfl⟩
    have he : d • z + v r = x := by
      apply e.injective
      rw [map_add, map_nsmul, hv]
      have hz' : e z = (y, 0) := e.apply_symm_apply _
      rw [hz']
      apply Prod.ext
      · change d • y + 0 = (e x).1
        rw [add_zero, hy]
      · change d • (0 : ℤ) + r = (e x).2
        simp [r]
    refine ⟨(r : ZMod d), ?_⟩
    change ZMod.lift d ⟨h, (hKer (d : ℤ)).mpr dvd_rfl⟩ (r : ZMod d) = a
    rw [ZMod.lift_coe]
    change b (v r) = a
    calc
      _ = b (d • z) + b (v r) := by rw [hz, zero_add]
      _ = b (d • z + v r) := (map_add b _ _).symm
      _ = a := by rw [he]; exact hx
  let root := (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let rootsIso : coefficientGroup K d ≅ AddCommGrpCat.of (ULift.{1} (ZMod d)) :=
    (AddEquiv.ulift.trans (root.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  exact (AddEquiv.ofBijective q ⟨hqi, hqs⟩).trans
    (cohomologyIso (X := Y K) ((constantSheaf (J (Y K)) G).mapIso rootsIso) 1)

end
end ManuscriptAudit.ProetaleLaurentCyclicHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleLaurentCyclicHOne.cyclicToHOne
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
