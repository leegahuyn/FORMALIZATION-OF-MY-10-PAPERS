import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineUnits

/-!
# Finite Kummer cohomology of the affine Weierstrass scheme

The actual derived first étale cohomology with roots of unity coefficients
identifies with torsion in first unit cohomology. Scalar units remove the
degree-zero term of the Kummer sequence.
-/

namespace ManuscriptAudit.WeierstrassAffineKummer

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open KummerCohomologySequence KummerSheafSequence KummerCohomologyDegreeTwo

noncomputable section

attribute [local instance] affineSiteHasExt SmallEtaleCohomologyComparison.fullSiteHasExt

private abbrev affineSite (R : CommRingCat.{0}) := Scheme.AffineEtale.topology (Spec R)

private abbrev integerConstant (R : CommRingCat.{0}) :=
  (constantSheaf (affineSite R) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))

/-- The actual Kummer inclusion identifies degree-one cohomology with unit
cohomology torsion over any affine base with surjective power on units. -/
def degreeOneKernelEquiv (R : CommRingCat.{0}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) (hUnits : Function.Surjective (fun u : Rˣ => u ^ d)) :
    Sheaf.H (powerKernel R d) 1 ≃+ killedBy (Sheaf.H (unitSheaf (Spec R)) 1) d := by
  let S := sequence (Spec R) d
  let hS := sequence_shortExact R d hpos hd
  let i : Sheaf.H (powerKernel R d) 1 →+ Sheaf.H (unitSheaf (Spec R)) 1 :=
    Sheaf.H.map S.f 1
  let g : Sheaf.H (unitSheaf (Spec R)) 1 →+ Sheaf.H (unitSheaf (Spec R)) 1 :=
    Sheaf.H.map S.g 1
  have hExact : Function.Exact i g := by
    have h := Ext.covariant_sequence_exact₂' (integerConstant R) hS 1
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hPower (y : Sheaf.H (unitSheaf (Spec R)) 1) : g y = d • y :=
    cohomologyPower_apply R d 1 y
  have hBoundary (z : Sheaf.H (unitSheaf (Spec R)) 0) :
      connecting R d hpos hd z = 0 := by
    let E := KummerAffineCohomology.degreeZeroUnits R
    obtain ⟨u, hu⟩ := hUnits (E z).toMul
    apply (degree_zero_exact R d hpos hd z).2
    refine ⟨E.symm (Additive.ofMul u), E.injective ?_⟩
    have h := KummerAffineCohomology.degreeZeroUnits_power R d (E.symm (Additive.ofMul u))
    change E (Sheaf.H.map (sheafPower (Spec R) d) 0 (E.symm (Additive.ofMul u))) =
      Additive.ofMul ((E (E.symm (Additive.ofMul u))).toMul ^ d) at h
    simpa only [E.apply_symm_apply, toMul_ofMul, hu, ofMul_toMul] using h
  let f : Sheaf.H (powerKernel R d) 1 →+ killedBy (Sheaf.H (unitSheaf (Spec R)) 1) d :=
    { toFun := fun x => ⟨i x, by
        change d • i x = 0
        rw [← hPower]
        exact (hExact (i x)).2 ⟨x, rfl⟩⟩
      map_zero' := Subtype.ext i.map_zero
      map_add' := fun x y => Subtype.ext (i.map_add x y) }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' : i x = i y := congrArg Subtype.val hxy
    have hz : i (x - y) = 0 := by rw [map_sub, hxy', sub_self]
    obtain ⟨z, hz'⟩ := (degree_one_exact R d hpos hd (x - y)).1 hz
    apply sub_eq_zero.mp
    exact hz'.symm.trans (hBoundary z)
  · intro y
    have hy : g y.val = 0 := (hPower y.val).trans y.property
    obtain ⟨x, hx⟩ := (hExact y.val).1 hy
    exact ⟨x, Subtype.ext hx⟩

private def killedByEquiv {U V : Type} [AddCommGroup U] [AddCommGroup V]
    (e : U ≃+ V) (d : ℕ) : killedBy U d ≃+ killedBy V d where
  toFun u := ⟨e u.val, by
    change d • e u.val = 0
    rw [← map_nsmul, show d • u.val = 0 from u.property, map_zero]⟩
  invFun v := ⟨e.symm v.val, by
    change d • e.symm v.val = 0
    rw [← map_nsmul, show d • v.val = 0 from v.property, map_zero]⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' u v := Subtype.ext (e.map_add u.val v.val)

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K)

private abbrev R := CommRingCat.of W.CoordinateRing

/-- On the full small étale site of a geometric affine Weierstrass curve,
constant power roots compute the torsion of actual first unit cohomology. -/
def geometricRootsHOneEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (Spec (R W)).smallEtaleTopology AddCommGrpCat.{0}).obj
      (KummerConstantCoefficients.coefficientGroup K d)) 1 ≃+
      killedBy (Sheaf.H (KummerUnitsSheaf.fullCoordinateUnitSheaf (Spec (R W))) 1) d := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : IsUnit (d : R W) := by
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (algebraMap K W.CoordinateRing)
  exact (SmallEtaleCohomologyComparison.cohomologyEquiv (R W) _ 1).symm.trans
    ((KummerAffineCohomology.degreeOneConstantRoots (K := K) (R W) d).trans
      ((degreeOneKernelEquiv (R W) d hpos hd
        (WeierstrassAffineUnits.unit_power_surjective W d hpos)).trans
        (killedByEquiv (KummerUnitsSheaf.unitCohomologyEquiv (R W) 1) d)))

end

end ManuscriptAudit.WeierstrassAffineKummer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffineKummer.degreeOneKernelEquiv,
      ``ManuscriptAudit.WeierstrassAffineKummer.geometricRootsHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
