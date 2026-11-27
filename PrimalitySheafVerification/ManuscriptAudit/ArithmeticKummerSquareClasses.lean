import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldSquareClasses

/-! Actual arithmetic H¹ of a finite field and its affine line with binary coefficients. -/

namespace ManuscriptAudit.ArithmeticKummerSquareClasses

open AlgebraicGeometry CategoryTheory KummerPIDUnitQuotient
open KummerConstantCoefficients

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K]

theorem primitiveNegOne (h₂ : (2 : K) ≠ 0) : IsPrimitiveRoot (-1 : K) 2 := by
  apply IsPrimitiveRoot.neg_one (ringChar K)
  intro h
  have hcast : ((2 : ℕ) : K) = 0 :=
    (CharP.cast_eq_zero_iff K (ringChar K) 2).mpr (by rw [h] <;> exact dvd_rfl)
  exact h₂ (by simpa using hcast)

private abbrev binary := AddCommGrpCat.of (ZMod 2)

private abbrev binaryHOne (R : Type) [CommRing R] :=
  Sheaf.H ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology
    AddCommGrpCat.{0}).obj binary) 1

def squareClassHOneEquiv (R : Type) [CommRing R] [Algebra K R]
    [IsDomain R] [IsPrincipalIdealRing R] (h₂ : (2 : K) ≠ 0) :
    (Additive Rˣ ⧸ powerSubgroup R 2) ≃+ binaryHOne R := by
  letI : NeZero (2 : ℕ) := ⟨by decide⟩
  letI : NeZero ((2 : ℕ) : K) := ⟨by simpa using h₂⟩
  letI : HasEnoughRootsOfUnity K 2 := ⟨⟨-1, primitiveNegOne K h₂⟩, rootsOfUnity.isCyclic K 2⟩
  let e : Additive (rootsOfUnity 2 K) ≃+ ZMod 2 :=
    (CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot (primitiveNegOne K h₂)).toAdditive
  let J := (Spec (CommRingCat.of R)).smallEtaleTopology
  let t := (constantSheaf J AddCommGrpCat.{0}).mapIso
    (e.toAddCommGrpIso : coefficientGroup K 2 ≅ binary)
  exact (rootsHOneEquiv K R 2).trans ((Sheaf.functorH J 1).mapIso t).addCommGroupIsoToAddEquiv

private def polynomialUnitEquiv : Kˣ ≃* (Polynomial K)ˣ :=
  MulEquiv.ofBijective (Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom)
    ⟨by
      intro a b hab
      apply Units.ext
      apply Polynomial.C_injective
      exact congrArg Units.val hab,
     by
      intro u
      obtain ⟨a, ha, hu⟩ := Polynomial.isUnit_iff.mp u.isUnit
      refine ⟨ha.unit, Units.ext ?_⟩
      change Polynomial.C (ha.unit : K) = (u : Polynomial K)
      rw [ha.unit_spec, hu]⟩

private theorem map_powerSubgroup (d : ℕ) :
    (powerSubgroup K d).map (polynomialUnitEquiv K).toAdditive.toAddMonoidHom =
      powerSubgroup (Polynomial K) d := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu⟩ := (mem_powerSubgroup d y).mp hy
    refine (mem_powerSubgroup d _).mpr ⟨polynomialUnitEquiv K u, ?_⟩
    rw [← map_pow, hu] <;> rfl
  · intro hx
    obtain ⟨u, hu⟩ := (mem_powerSubgroup d x).mp hx
    let a := (polynomialUnitEquiv K).symm u
    refine ⟨Additive.ofMul (a ^ d), (mem_powerSubgroup d _).mpr ⟨a, rfl⟩, ?_⟩
    apply Additive.ext
    show polynomialUnitEquiv K (a ^ d) = x.toMul
    rw [map_pow, MulEquiv.apply_symm_apply, hu]

theorem residue_binary_HOne_card [Finite K] (h₂ : (2 : K) ≠ 0) :
    Nat.card (binaryHOne K) = 2 :=
  (Nat.card_congr (squareClassHOneEquiv K K h₂).toEquiv).symm.trans
    (FiniteFieldSquareClasses.squareClass_card K h₂)

theorem affineLine_binary_HOne_card [Finite K] (h₂ : (2 : K) ≠ 0) :
    Nat.card (binaryHOne (Polynomial K)) = 2 := by
  let e := QuotientAddGroup.congr (powerSubgroup K 2) (powerSubgroup (Polynomial K) 2)
    (polynomialUnitEquiv K).toAdditive (map_powerSubgroup K 2)
  exact (Nat.card_congr (e.trans (squareClassHOneEquiv K (Polynomial K) h₂)).toEquiv).symm.trans
    (FiniteFieldSquareClasses.squareClass_card K h₂)

private def cyclicEquivOfCardTwo (G : Type) [AddGroup G] (h : Nat.card G = 2) :
    ZMod 2 ≃+ G := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hCyc := isAddCyclic_of_prime_card h
  exact (ZMod.ringEquivCongr h.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv hCyc)

def residueBinaryHOneEquiv [Finite K] (h₂ : (2 : K) ≠ 0) :
    ZMod 2 ≃+ binaryHOne K :=
  cyclicEquivOfCardTwo _ (residue_binary_HOne_card K h₂)

def affineLineBinaryHOneEquiv [Finite K] (h₂ : (2 : K) ≠ 0) :
    ZMod 2 ≃+ binaryHOne (Polynomial K) :=
  cyclicEquivOfCardTwo _ (affineLine_binary_HOne_card K h₂)

end
end ManuscriptAudit.ArithmeticKummerSquareClasses

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticKummerSquareClasses.primitiveNegOne,
      ``ManuscriptAudit.ArithmeticKummerSquareClasses.squareClassHOneEquiv,
      ``ManuscriptAudit.ArithmeticKummerSquareClasses.residue_binary_HOne_card,
      ``ManuscriptAudit.ArithmeticKummerSquareClasses.affineLine_binary_HOne_card,
      ``ManuscriptAudit.ArithmeticKummerSquareClasses.residueBinaryHOneEquiv,
      ``ManuscriptAudit.ArithmeticKummerSquareClasses.affineLineBinaryHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
