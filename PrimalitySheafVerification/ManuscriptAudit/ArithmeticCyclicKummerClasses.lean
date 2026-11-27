import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticKummerSquareClasses

/-! Native cyclic étale H¹ over finite fields with a chosen primitive root. -/

namespace ManuscriptAudit.ArithmeticCyclicKummerClasses

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open KummerPIDUnitQuotient KummerConstantCoefficients
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] (d : ℕ)

private def powerMap : Additive Kˣ →+ Additive Kˣ where
  toFun u := Additive.ofMul (u.toMul ^ d)
  map_zero' := by simp
  map_add' u v := by change Additive.ofMul ((u.toMul * v.toMul) ^ d) = _; rw [mul_pow] <;> rfl

private def kernelRootsEquiv : (powerMap K d).ker ≃ rootsOfUnity d K where
  toFun u := ⟨u.val.toMul, by
    change u.val.toMul ^ d = 1
    exact congrArg Additive.toMul u.property⟩
  invFun u := ⟨Additive.ofMul u.val, by
    change Additive.ofMul (u.val ^ d) = 0
    exact congrArg Additive.ofMul (show u.val ^ d = 1 from u.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem powerMap_range : (powerMap K d).range = powerSubgroup K d := by
  ext x
  rw [AddMonoidHom.mem_range, mem_powerSubgroup]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.toMul, congrArg Additive.toMul hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩

theorem powerClass_card [Finite K] [NeZero d] {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    Nat.card (Additive Kˣ ⧸ powerSubgroup K d) = d := by
  let f := powerMap K d
  have hKer : Nat.card f.ker = d :=
    (Nat.card_congr (kernelRootsEquiv K d)).trans hζ.card_rootsOfUnity
  have hRange : f.ker.index = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have h₁ := f.ker.index_mul_card
  rw [hRange, hKer] at h₁
  have h₂ := f.range.card_mul_index
  have hIndex : f.range.index = d :=
    mul_left_cancel₀ (Nat.card_pos (α := f.range)).ne' (h₂.trans h₁.symm)
  rw [← powerMap_range]
  exact hIndex

def powerClassEquiv [Finite K] [NeZero d] {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ZMod d ≃+ (Additive Kˣ ⧸ powerSubgroup K d) := by
  let Q := Additive Kˣ ⧸ powerSubgroup K d
  have hQ : IsAddCyclic Q :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' (powerSubgroup K d)) QuotientAddGroup.mk_surjective
  exact powerClass_card K d hζ ▸ zmodAddCyclicAddEquiv hQ

private abbrev cyclicHOne (R : Type) [CommRing R] :=
  Sheaf.H ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology
    AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1

def powerClassHOneEquiv (R : Type) [CommRing R] [Algebra K R]
    [IsDomain R] [IsPrincipalIdealRing R] [NeZero d] [NeZero (d : K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    (Additive Rˣ ⧸ powerSubgroup R d) ≃+ cyclicHOne d R := by
  letI : HasEnoughRootsOfUnity K d := ⟨⟨ζ, hζ⟩, rootsOfUnity.isCyclic K d⟩
  let e : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot hζ).toAdditive
  let J := (Spec (CommRingCat.of R)).smallEtaleTopology
  let t := (constantSheaf J AddCommGrpCat.{0}).mapIso
    (e.toAddCommGrpIso : coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  exact (rootsHOneEquiv K R d).trans ((Sheaf.functorH J 1).mapIso t).addCommGroupIsoToAddEquiv

def finiteResidueHOneEquiv [Finite K] [NeZero d] [NeZero (d : K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ZMod d ≃+ cyclicHOne d K :=
  (powerClassEquiv K d hζ).trans (powerClassHOneEquiv K d K hζ)

end
end ManuscriptAudit.ArithmeticCyclicKummerClasses

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticCyclicKummerClasses.powerClass_card,
      ``ManuscriptAudit.ArithmeticCyclicKummerClasses.powerClassEquiv,
      ``ManuscriptAudit.ArithmeticCyclicKummerClasses.powerClassHOneEquiv,
      ``ManuscriptAudit.ArithmeticCyclicKummerClasses.finiteResidueHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
