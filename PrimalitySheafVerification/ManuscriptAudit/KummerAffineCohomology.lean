import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerCohomologySequence
import PrimalitySheafVerification.ManuscriptAudit.KummerKernel
import PrimalitySheafVerification.ManuscriptAudit.KummerUnitsSheaf

/-!
# Global units and constant coefficients in low-degree Kummer cohomology

The first power map in the native Kummer sequence is the power map on
the actual affine coordinate-ring units. The next term uses the actual
constant roots-of-unity sheaf.
-/

namespace ManuscriptAudit.KummerAffineCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open KummerCohomologySequence KummerConstantCoefficients KummerKernel
open KummerSheafSequence KummerUnitsPresheaf KummerUnitsSheaf

noncomputable section

private abbrev affineTopology (R : CommRingCat.{0}) := Scheme.AffineEtale.topology (Spec R)

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

private def affineTerminal (R : CommRingCat.{0}) : (Spec R).AffineEtale :=
  Scheme.AffineEtale.mk (𝟙 (Spec R))

private def affineTerminalArrow (R : CommRingCat.{0}) (U : (Spec R).AffineEtale) :
    U ⟶ affineTerminal R :=
  MorphismProperty.CostructuredArrow.homMk (Scheme.Spec.preimage U.hom) trivial
    (by simp [affineTerminal])

private def affineTerminal_isTerminal (R : CommRingCat.{0}) : IsTerminal (affineTerminal R) := by
  refine IsTerminal.ofUniqueHom (affineTerminalArrow R) ?_
  intro U f
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Scheme.Spec.map_injective
  have hf : Scheme.Spec.map f.left ≫ 𝟙 (Spec R) = U.hom := by
    simpa [affineTerminal] using f.w
  simpa [affineTerminalArrow] using hf

private def nativePower (R : CommRingCat.{0}) (d : ℕ) :
    coordinateUnitSheaf (Spec R) ⟶ coordinateUnitSheaf (Spec R) :=
  ⟨power (Spec R) d⟩

/-- Degree-zero cohomology of the Kummer unit sheaf is the coordinate-ring
unit group. -/
def degreeZeroUnits (R : CommRingCat.{0}) :
    Sheaf.H (unitSheaf (Spec R)) 0 ≃+ Additive Rˣ :=
  (((Sheaf.functorH (affineTopology R) 0).mapIso
    (coordinateUnitSheafIso (Spec R)).symm).addCommGroupIsoToAddEquiv).trans
      (Sheaf.H.equiv₀ (coordinateUnitSheaf (Spec R)) (affineTerminal_isTerminal R))

/-- Under the degree-zero identification, the sheaf power map acts by the
usual (d)-th power of a unit. -/
theorem degreeZeroUnits_power (R : CommRingCat.{0}) (d : ℕ)
    (x : Sheaf.H (unitSheaf (Spec R)) 0) :
    degreeZeroUnits R (Sheaf.H.map (sheafPower (Spec R) d) 0 x) =
      Additive.ofMul ((degreeZeroUnits R x).toMul ^ d) := by
  let e := coordinateUnitSheafIso (Spec R)
  let n := nativePower R d
  let g := sheafPower (Spec R) d
  have hn : n ≫ e.hom = e.hom ≫ g := by
    simpa only [Functor.id_map] using
      (sheafificationNatIso (affineTopology R) AddCommGrpCat.{0}).hom.naturality n
  have hm : g ≫ e.inv = e.inv ≫ n := by
    apply (cancel_mono e.hom).mp
    calc
      (g ≫ e.inv) ≫ e.hom = g := by simp
      _ = e.inv ≫ e.hom ≫ g := by simp
      _ = (e.inv ≫ n) ≫ e.hom := by rw [Category.assoc, hn]
  let ev := Sheaf.H.equiv₀ (coordinateUnitSheaf (Spec R)) (affineTerminal_isTerminal R)
  change ev (Sheaf.H.map e.inv 0 (Sheaf.H.map g 0 x)) =
    Additive.ofMul ((ev (Sheaf.H.map e.inv 0 x)).toMul ^ d)
  rw [← Sheaf.H.map_comp_apply, hm, Sheaf.H.map_comp_apply, ← Sheaf.H.equiv₀_naturality] <;> rfl

/-- The source of the degree-one Kummer sequence is actual cohomology of the
constant sheaf of coefficient roots. -/
def degreeOneConstantRoots {K : Type} [Field K] [IsAlgClosed K]
    (R : CommRingCat.{0}) [Algebra K R] (d : ℕ) [NeZero d] [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (affineTopology R) AddCommGrpCat.{0}).obj
      (coefficientGroup K d)) 1 ≃+ Sheaf.H (powerKernel R d) 1 :=
  ((Sheaf.functorH (affineTopology R) 1).mapIso
    (constantPowerKernelIso (K := K) R d)).addCommGroupIsoToAddEquiv

/-- The connecting map from units to actual constant-coefficient H¹. -/
def unitBoundary {K : Type} [Field K] [IsAlgClosed K]
    (R : CommRingCat.{0}) [Algebra K R] (d : ℕ) [NeZero d] [NeZero (d : K)]
    (hpos : 0 < d) (hd : IsUnit (d : R)) :
    Additive Rˣ →+ Sheaf.H ((constantSheaf (affineTopology R) AddCommGrpCat.{0}).obj
      (coefficientGroup K d)) 1 :=
  (degreeOneConstantRoots (K := K) R d).symm.toAddMonoidHom.comp
    ((connecting R d hpos hd).comp (degreeZeroUnits R).symm.toAddMonoidHom)

/-- A unit has zero connecting class exactly when it is a (d)-th power. -/
theorem unitBoundary_eq_zero_iff {K : Type} [Field K] [IsAlgClosed K]
    (R : CommRingCat.{0}) [Algebra K R] (d : ℕ) [NeZero d] [NeZero (d : K)]
    (hpos : 0 < d) (hd : IsUnit (d : R)) (y : Additive Rˣ) :
    unitBoundary (K := K) R d hpos hd y = 0 ↔ ∃ x : Rˣ, x ^ d = y.toMul := by
  let E := degreeZeroUnits R
  let G := degreeOneConstantRoots (K := K) R d
  let δ := connecting R d hpos hd
  let P := Sheaf.H.map (sheafPower (Spec R) d) 0
  have hExact : Function.Exact P δ := degree_zero_exact R d hpos hd
  change G.symm (δ (E.symm y)) = 0 ↔ _
  rw [← G.symm.map_zero, G.symm.injective.eq_iff]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (hExact (E.symm y)).mp h
    refine ⟨(E x).toMul, ?_⟩
    have hp := degreeZeroUnits_power R d x
    change E (P x) = Additive.ofMul ((E x).toMul ^ d) at hp
    rw [hx, E.apply_symm_apply] at hp
    exact (congrArg Additive.toMul hp).symm
  · rintro ⟨x, hx⟩
    apply (hExact (E.symm y)).mpr
    refine ⟨E.symm (Additive.ofMul x), E.injective ?_⟩
    have hp := degreeZeroUnits_power R d (E.symm (Additive.ofMul x))
    change E (P (E.symm (Additive.ofMul x))) =
      Additive.ofMul ((E (E.symm (Additive.ofMul x))).toMul ^ d) at hp
    simpa only [E.apply_symm_apply, Additive.toMul_ofMul, hx, Additive.ofMul_toMul] using hp

end

end ManuscriptAudit.KummerAffineCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerAffineCohomology.degreeZeroUnits,
      ``ManuscriptAudit.KummerAffineCohomology.degreeZeroUnits_power,
      ``ManuscriptAudit.KummerAffineCohomology.degreeOneConstantRoots,
      ``ManuscriptAudit.KummerAffineCohomology.unitBoundary_eq_zero_iff] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
