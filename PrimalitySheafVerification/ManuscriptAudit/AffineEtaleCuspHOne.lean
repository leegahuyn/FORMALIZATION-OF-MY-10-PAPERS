import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.SetTheory.Cardinal.Finite
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleProductDescent
import PrimalitySheafVerification.ManuscriptAudit.LaurentEtaleCohomology

/-!
# Native affine étale degree-one groups for the cusp comparison

The coordinate rings of the affine line and the cusp with its origin removed
are principal ideal domains. Their unit sheaves have trivial degree-one
cohomology, which gives the corresponding Kummer computations.
-/

namespace ManuscriptAudit.AffineEtaleCuspHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

private abbrev affineSite (R : CommRingCat.{0}) := Scheme.AffineEtale.topology (Spec R)

/-- The sheafified and coordinate units give the same native vanishing over a PID. -/
theorem unitSheaf_HOne_subsingleton_of_pid (R : Type) [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] :
    Subsingleton (Sheaf.H (KummerSheafSequence.unitSheaf (Spec (CommRingCat.of R))) 1) := by
  let A := CommRingCat.of R
  have hCoordinate : Subsingleton (Sheaf.H (KummerUnitsSheaf.coordinateUnitSheaf (Spec A)) 1) :=
    AffineEtaleProductDescent.affineUnitH1_subsingleton R
  let e := ((Sheaf.functorH (affineSite A) 1).mapIso
    (KummerUnitsSheaf.coordinateUnitSheafIso (Spec A))).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => e.symm.injective (hCoordinate.elim _ _)⟩

variable (K : Type) [Field K]

private abbrev cuspCoordinate := Localization.Away (CuspPunctured.cuspSquare K)

private theorem cuspCoordinate_domain_and_pid :
    IsDomain (cuspCoordinate K) ∧ IsPrincipalIdealRing (cuspCoordinate K) := by
  let M := Submonoid.powers (Polynomial.X : Polynomial K)
  have hM : M ≤ (Polynomial K)⁰ := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  letI : IsDomain (LaurentPolynomial K) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (LaurentPolynomial K) hM
  letI : IsPrincipalIdealRing (LaurentPolynomial K) := ⟨fun I => by
    rw [← IsLocalization.map_under M (LaurentPolynomial K) I]
    exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (LaurentPolynomial K))
      (inferInstance : (I.under (Polynomial K)).IsPrincipal)⟩
  let e := CuspPunctured.paper2_cusp_punctured_coordinate_equiv K
  refine ⟨MulEquiv.isDomain (LaurentPolynomial K) e.toRingEquiv.toMulEquiv, ⟨fun I => ?_⟩⟩
  let J := Ideal.comap e.symm.toRingHom I
  have hJ : (Ideal.map e.symm.toRingHom J).IsPrincipal :=
    Submodule.IsPrincipal.map_ringHom e.symm.toRingHom (inferInstance : J.IsPrincipal)
  exact (Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective I) ▸ hJ

private abbrev lineRing : CommRingCat.{0} := CommRingCat.of (Polynomial K)
private abbrev cuspRing : CommRingCat.{0} := CommRingCat.of (cuspCoordinate K)

variable [IsAlgClosed K]

/-- Native affine-line H¹ with constant roots-of-unity coefficients is zero. -/
theorem affineLine_roots_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (affineSite (lineRing K))
      AddCommGrpCat.{0}).obj (KummerConstantCoefficients.coefficientGroup K d)) 1) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : IsUnit (d : Polynomial K) := by
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (algebraMap K (Polynomial K))
  exact LaurentEtaleCohomology.affineLine_HOne_roots_subsingleton_of_unitHOne K d hpos hd
    (unitSheaf_HOne_subsingleton_of_pid (Polynomial K))

/-- The same affine-line vanishing with the constant cyclic coefficient group. -/
theorem affineLine_cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (affineSite (lineRing K))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1) := by
  have hRoots := affineLine_roots_HOne_subsingleton K d
  let r : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let e := (constantSheaf (affineSite (lineRing K)) AddCommGrpCat.{0}).mapIso
    (r.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let h := ((Sheaf.functorH (affineSite (lineRing K)) 1).mapIso e).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => h.symm.injective (hRoots.elim _ _)⟩

/-- The punctured cusp has native H¹ isomorphic to the constant cyclic
coefficient group for degree at least two and nonzero in the field. -/
def cuspPuncturedCyclicHOneEquiv (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ZMod d ≃+ Sheaf.H ((constantSheaf (affineSite (cuspRing K)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1 := by
  obtain ⟨hDomain, hPID⟩ := cuspCoordinate_domain_and_pid K
  letI := hDomain
  letI := hPID
  exact Classical.choice
    (LaurentEtaleCohomology.cusp_punctured_cyclic_HOne_equiv_of_unitHOne K d hdeg
      (unitSheaf_HOne_subsingleton_of_pid (cuspCoordinate K)))

theorem affineLine_cyclic_HOne_card (d : ℕ) [NeZero (d : K)] :
    Nat.card (Sheaf.H ((constantSheaf (affineSite (lineRing K))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1) = 1 := by
  letI := affineLine_cyclic_HOne_subsingleton K d
  exact Nat.card_unique

theorem cuspPunctured_cyclic_HOne_card (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    Nat.card (Sheaf.H ((constantSheaf (affineSite (cuspRing K))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1) = d := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  calc
    _ = Nat.card (ZMod d) := Nat.card_congr (cuspPuncturedCyclicHOneEquiv K d hdeg).symm.toEquiv
    _ = d := by rw [Nat.card_eq_fintype_card, ZMod.card]

end

end ManuscriptAudit.AffineEtaleCuspHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid,
    ``ManuscriptAudit.AffineEtaleCuspHOne.affineLine_roots_HOne_subsingleton,
    ``ManuscriptAudit.AffineEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton,
    ``ManuscriptAudit.AffineEtaleCuspHOne.cuspPuncturedCyclicHOneEquiv,
    ``ManuscriptAudit.AffineEtaleCuspHOne.affineLine_cyclic_HOne_card,
    ``ManuscriptAudit.AffineEtaleCuspHOne.cuspPunctured_cyclic_HOne_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
