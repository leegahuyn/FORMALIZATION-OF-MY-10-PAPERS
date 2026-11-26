import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportLowDegrees
import PrimalitySheafVerification.ManuscriptAudit.FiveTermEuler

/-!
# The degree-zero and degree-one Euler difference with finite coefficients

The native étale cohomology groups with constant ZMod coefficients have
the canonical scalar action supplied by their annihilation by the prime.
The five-term sequence from the proper compactification then has Euler
difference one whenever its low-degree groups have finite dimension.
-/

namespace ManuscriptAudit.CuspCompactSupportEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open OpenEtaleExtension CuspCompactSupportSequence CuspCompactSupportHigherComparison
open CuspCompactSupportLowDegrees SmallEtaleGeometricBaseChange Opposite
open scoped BigOperators

universe u

noncomputable section

variable (K : Type u) [Field K] [IsSepClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

private abbrev G := AddCommGrpCat.{u}
private abbrev coeff : G.{u} := AddCommGrpCat.of (ULift.{u} (ZMod ℓ))

private theorem map_annihilated_id {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] (X : C)
    (h : ℓ • 𝟙 X = 0) : ℓ • 𝟙 (F.obj X) = 0 := by
  calc
    ℓ • 𝟙 (F.obj X) = F.map (ℓ • 𝟙 X) := by rw [F.map_nsmul, F.map_id]
    _ = 0 := by rw [h, F.map_zero]

private theorem coeff_annihilated : ℓ • 𝟙 (coeff ℓ) = 0 := by
  ext x
  apply ULift.ext
  change ℓ • x.down = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem constantSheaf_additive (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology G.{u}).Additive := by
  let J := X.smallEtaleTopology
  let T : X.Etale := ⊤_ X.Etale
  let a := constantSheafAdj J G.{u} (terminalIsTerminal (C := X.Etale))
  letI : ((sheafSections J G.{u}).obj (op T)).Additive := ⟨by intros; rfl⟩
  exact a.left_adjoint_additive

private theorem extensionByZero_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extensionByZero j G.{u}).Additive := by
  letI : (restriction j G.{u}).Additive := ⟨by intros; rfl⟩
  exact (abelianExtensionByZeroAdjunction j).left_adjoint_additive

private theorem extensionCohomology_annihilated {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (x : Sheaf.H
      ((extensionByZero j G.{u}).obj ((constantSheaf U.smallEtaleTopology G.{u}).obj (coeff ℓ))) n) :
    ℓ • x = 0 := by
  let F := constantSheaf U.smallEtaleTopology G.{u}
  let E := extensionByZero j G.{u}
  letI : F.Additive := constantSheaf_additive U
  letI : E.Additive := extensionByZero_additive j
  have hf := map_annihilated_id ℓ F (coeff ℓ) (coeff_annihilated ℓ)
  have he := map_annihilated_id ℓ E (F.obj (coeff ℓ)) hf
  have hH := map_annihilated_id ℓ (Sheaf.functorH X.smallEtaleTopology n)
    (E.obj (F.obj (coeff ℓ))) he
  exact ConcreteCategory.congr_hom hH x

local instance cuspModule (n : ℕ) :
    Module (ZMod ℓ) (cuspHc K (coeff ℓ) n) := by
  letI := CuspProperCompactification.affineOpen_isOpenImmersion K
  exact AddCommGroup.zmodModule
    (extensionCohomology_annihilated ℓ (CuspProperCompactification.affineOpen K) n)

local instance punctureModule (n : ℕ) :
    Module (ZMod ℓ) (punctureHc K (coeff ℓ) n) := by
  letI := CuspProperCompactification.affineOpen_isOpenImmersion K
  exact AddCommGroup.zmodModule (extensionCohomology_annihilated ℓ
    ((cuspPuncturedOpen K).ι ≫ CuspProperCompactification.affineOpen K) n)

private abbrev boundaryHZero :=
  Sheaf.H (compactSupportSequence K (coeff ℓ)).X₃ 0

local instance boundaryModule : Module (ZMod ℓ) (boundaryHZero K ℓ) := by
  apply AddCommGroup.zmodModule
  intro x
  let e := compactSupportBoundaryHZeroEquiv K (coeff ℓ)
  apply e.injective
  rw [map_nsmul, map_zero]
  exact ConcreteCategory.congr_hom (coeff_annihilated ℓ) (e x)

private def toBaseCoeff :
    boundaryHZero K ℓ ≃ₗ[ZMod ℓ] ZMod ℓ := by
  let ul : ULift.{u} (ZMod ℓ) ≃+ ZMod ℓ :=
    { toFun := ULift.down, invFun := ULift.up, left_inv := by intro x; rfl,
      right_inv := by intro x; rfl, map_add' := by intros; rfl }
  let e := (compactSupportBoundaryHZeroEquiv K (coeff ℓ)).trans ul
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective

/-- The checked localization contributes one to the Euler difference in degrees zero and one. -/
theorem lowDegreeEulerDifference
    [FiniteDimensional (ZMod ℓ) (punctureHc K (coeff ℓ) 0)]
    [FiniteDimensional (ZMod ℓ) (cuspHc K (coeff ℓ) 0)]
    [FiniteDimensional (ZMod ℓ) (punctureHc K (coeff ℓ) 1)]
    [FiniteDimensional (ZMod ℓ) (cuspHc K (coeff ℓ) 1)] :
    ((Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) 0) : ℤ) -
      Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) 1)) -
    ((Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) 0) : ℤ) -
      Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) 1)) = 1 := by
  let s := compactSupportSequence K (coeff ℓ)
  let e := toBaseCoeff K ℓ
  letI := e.symm.finiteDimensional
  obtain ⟨hf, hfg, hgd, hdi, hi⟩ := compactSupportFiveTerm K (coeff ℓ)
  have h := FiveTermEuler.alternating_finrank
    ((Sheaf.H.map s.f 0).toZModLinearMap ℓ)
    ((Sheaf.H.map s.g 0).toZModLinearMap ℓ)
    ((connecting K (coeff ℓ)).toZModLinearMap ℓ)
    ((Sheaf.H.map s.f 1).toZModLinearMap ℓ) hf hfg hgd hdi hi
  simpa only [e.finrank_eq, Module.finrank_self, Nat.cast_one] using h

/-- The higher comparison preserves the dimensions in every degree at least two. -/
theorem higherFinrank_eq (n : ℕ) :
    Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) (n + 2)) =
      Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) (n + 2)) := by
  let e := compactSupportHigherEquiv K (coeff ℓ) n
  exact (LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective).finrank_eq

/-- Every common finite truncation of the two Euler sums has difference one. -/
theorem truncatedEulerDifference
    [FiniteDimensional (ZMod ℓ) (punctureHc K (coeff ℓ) 0)]
    [FiniteDimensional (ZMod ℓ) (cuspHc K (coeff ℓ) 0)]
    [FiniteDimensional (ZMod ℓ) (punctureHc K (coeff ℓ) 1)]
    [FiniteDimensional (ZMod ℓ) (cuspHc K (coeff ℓ) 1)] (N : ℕ) :
    (((Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) 0) : ℤ) -
      Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) 1)) +
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) (n + 2))) -
    (((Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) 0) : ℤ) -
      Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) 1)) +
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) (n + 2))) = 1 := by
  have hTail :
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) (n + 2))) =
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) (n + 2))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [higherFinrank_eq K ℓ n]
  rw [hTail]
  have h := lowDegreeEulerDifference K ℓ
  omega

end

end ManuscriptAudit.CuspCompactSupportEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportEuler.lowDegreeEulerDifference,
      ``ManuscriptAudit.CuspCompactSupportEuler.higherFinrank_eq,
      ``ManuscriptAudit.CuspCompactSupportEuler.truncatedEulerDifference] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
