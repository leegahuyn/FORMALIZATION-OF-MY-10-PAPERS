import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Degree-two Kummer torsion on the affine étale site

When the unit sheaf has zero degree-one cohomology, the native Kummer
sequence identifies degree-two root cohomology with the subgroup killed
by the degree. The affine-line specialization uses the proved vanishing
for a principal ideal domain.
-/

namespace ManuscriptAudit.KummerCohomologyDegreeTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open KummerCohomologySequence KummerSheafSequence KummerUnitsPresheaf

noncomputable section

universe u

attribute [local instance] affineSiteHasExt SmallEtaleCohomologyComparison.fullSiteHasExt

private abbrev affineSite (R : CommRingCat.{u}) := Scheme.AffineEtale.topology (Spec R)

private abbrev integerConstant (R : CommRingCat.{u}) :=
  (constantSheaf (affineSite R) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

/-- The subgroup of elements annihilated by multiplication by `d`. -/
def killedBy (A : Type u) [AddCommGroup A] (d : ℕ) : AddSubgroup A where
  carrier := {x | d • x = 0}
  zero_mem' := nsmul_zero _
  add_mem' {x y} hx hy := by
    change d • x = 0 at hx
    change d • y = 0 at hy
    change d • (x + y) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' {x} hx := by
    change d • x = 0 at hx
    change d • (-x) = 0
    have h : d • (0 - x) = 0 := by rw [nsmul_sub, nsmul_zero, hx, sub_zero]
    simpa only [zero_sub] using h

private theorem presheafPower_eq_nsmul_id (X : Scheme.{u}) (d : ℕ) :
    power X d = d • 𝟙 (units X) := by
  apply NatTrans.ext
  funext U
  rw [NatTrans.app_nsmul]
  apply AddCommGrpCat.ext
  intro x
  let a : Additive (coordinateRing U.unop)ˣ := x
  change Additive.ofMul (a.toMul ^ d) = d • a
  exact Additive.ofMul_pow d a.toMul

theorem sheafPower_eq_nsmul_id (X : Scheme.{u}) (d : ℕ) :
    sheafPower X d = d • 𝟙 (unitSheaf X) := by
  let F := presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}
  change F.map (power X d) = _
  rw [presheafPower_eq_nsmul_id, Functor.map_nsmul]
  exact congrArg (fun f => d • f) (F.map_id (units X))

/-- The power map acts as ordinary multiplication by the degree on all cohomology groups. -/
theorem cohomologyPower_apply (R : CommRingCat.{u}) (d n : ℕ)
    (x : Sheaf.H (unitSheaf (Spec R)) n) :
    Sheaf.H.map (sheafPower (Spec R) d) n x = d • x := by
  let F := Sheaf.functorH (affineSite R) n
  change (F.map (sheafPower (Spec R) d)).hom x = _
  rw [sheafPower_eq_nsmul_id, Functor.map_nsmul]
  have hId : F.map (𝟙 (unitSheaf (Spec R))) = 𝟙 (F.obj (unitSheaf (Spec R))) :=
    F.map_id (unitSheaf (Spec R))
  rw [hId] <;> rfl

/-- If the unit sheaf has zero first cohomology, the Kummer inclusion
identifies its coefficient's second cohomology with the actual torsion subgroup. -/
def degreeTwoKernelEquiv (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) (h₁ : Subsingleton (Sheaf.H (unitSheaf (Spec R)) 1)) :
    Sheaf.H (powerKernel R d) 2 ≃+ killedBy (Sheaf.H (unitSheaf (Spec R)) 2) d := by
  let S := sequence (Spec R) d
  let hS := sequence_shortExact R d hpos hd
  let i : Sheaf.H (powerKernel R d) 2 →+ Sheaf.H (unitSheaf (Spec R)) 2 :=
    Sheaf.H.map S.f 2
  let g : Sheaf.H (unitSheaf (Spec R)) 2 →+ Sheaf.H (unitSheaf (Spec R)) 2 :=
    Sheaf.H.map S.g 2
  have hExact : Function.Exact i g := by
    have h := Ext.covariant_sequence_exact₂' (integerConstant R) hS 2
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hPower (y : Sheaf.H (unitSheaf (Spec R)) 2) : g y = d • y :=
    cohomologyPower_apply R d 2 y
  let f : Sheaf.H (powerKernel R d) 2 →+ killedBy (Sheaf.H (unitSheaf (Spec R)) 2) d :=
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
    have hz' : (x - y).comp (Ext.mk₀ S.f) (add_zero 2) = 0 := hz
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁
      (X := integerConstant R) hS (x - y) hz' (show 1 + 1 = 2 by rfl)
    have ht₀ : t = 0 := h₁.allEq _ _
    apply sub_eq_zero.mp
    rw [← ht, ht₀, Ext.zero_comp] <;> rfl
  · intro y
    have hy : d • (y : Sheaf.H (unitSheaf (Spec R)) 2) = 0 := y.property
    obtain ⟨x, hx⟩ := (hExact y).1 ((hPower y).trans hy)
    exact ⟨x, Subtype.ext hx⟩

private abbrev lineRing (K : Type) [Field K] := CommRingCat.of (Polynomial K)

/-- On the actual full small étale site of the affine line, degree-two
cohomology with cyclic coefficients identifies with Kummer unit torsion. -/
def affineLineCyclicHTwoEquiv (K : Type) [Field K] [IsAlgClosed K]
    (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (Spec (lineRing K)).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 2 ≃+
        killedBy (Sheaf.H (unitSheaf (Spec (lineRing K))) 2) d := by
  let R := lineRing K
  letI : NeZero d := NeZero.of_neZero_natCast K
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : IsUnit (d : R) := by
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (algebraMap K (Polynomial K))
  let eRoots : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let eCoefficients := (constantSheaf (affineSite R) AddCommGrpCat.{0}).mapIso
    (eRoots.toAddCommGrpIso :
      KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let eSheaves := eCoefficients.symm ≪≫ KummerKernel.constantPowerKernelIso (K := K) R d
  let eH := ((Sheaf.functorH (affineSite R) 2).mapIso eSheaves).addCommGroupIsoToAddEquiv
  exact (SmallEtaleCohomologyComparison.cohomologyEquiv R (AddCommGrpCat.of (ZMod d)) 2).symm.trans
    (eH.trans (degreeTwoKernelEquiv R d hpos hd
      (AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid (Polynomial K))))

end

end ManuscriptAudit.KummerCohomologyDegreeTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerCohomologyDegreeTwo.sheafPower_eq_nsmul_id,
      ``ManuscriptAudit.KummerCohomologyDegreeTwo.cohomologyPower_apply,
      ``ManuscriptAudit.KummerCohomologyDegreeTwo.degreeTwoKernelEquiv,
      ``ManuscriptAudit.KummerCohomologyDegreeTwo.affineLineCyclicHTwoEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
