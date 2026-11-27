import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerTorsionFree
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineLineCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction

/-! Native cyclic degree-two cohomology identifies with the corresponding
torsion of unit cohomology when native Pic is zero. -/

namespace ManuscriptAudit.ProetaleKummerHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (sequence_shortExact constantKernelIso)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerTorsionFree (map_power_apply)
open ProetaleUnitSheaf (unitSheaf)
open ProetaleAffineTensor (spectrum)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual degree-two Kummer map on native units defines the d-torsion subgroup. -/
abbrev unitsTorsion (X : Scheme.{0}) (d : ℕ) : AddSubgroup (Sheaf.H (unitSheaf X) 2) :=
  (Sheaf.H.map (power X d) 2).ker

theorem mem_unitsTorsion (X : Scheme.{0}) (d : ℕ) (a : Sheaf.H (unitSheaf X) 2) :
    a ∈ unitsTorsion X d ↔ d • a = 0 := by
  change Sheaf.H.map (power X d) 2 a = 0 ↔ _
  rw [map_power_apply]

variable {X : Scheme.{0}} {K : Type} [Field K]
variable (k : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
  [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

/-- The genuine Kummer inclusion matches degree-two root cohomology with the
d-torsion in the native unit group, once native Pic vanishes. -/
def rootsEquivUnitsTorsion (vanishing : Subsingleton (Sheaf.H (unitSheaf X) 1)) :
    Sheaf.H ((constantSheaf (J X) G).obj (coefficientGroup K d)) 2 ≃+ unitsTorsion X d := by
  let T := (constantSheaf (J X) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  let h := sequence_shortExact k d
  let f := Sheaf.H.map (kernel.ι (power X d)) 2
  let q := Sheaf.H.map (power X d) 2
  let δ : Sheaf.H (unitSheaf X) 1 →+ Sheaf.H (kernel (power X d)) 2 := h.extClass.postcomp T rfl
  have ex₀ : Function.Exact δ f :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₁' T h 1 2 rfl)
  have ex₁ : Function.Exact f q :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₂' T h 2)
  let g : Sheaf.H (kernel (power X d)) 2 →+ unitsTorsion X d :=
    f.codRestrict _ (fun a ↦ (ex₁ (f a)).mpr ⟨a, rfl⟩)
  have hi : Function.Injective g := by
    intro a b hEq
    have hEq' : f a = f b := congrArg Subtype.val hEq
    apply sub_eq_zero.mp
    have hzero : f (a - b) = 0 := by rw [map_sub, hEq', sub_self]
    obtain ⟨c, hc⟩ := (ex₀ (a - b)).mp hzero
    have hc₀ : c = 0 := vanishing.elim _ _
    rw [hc₀, map_zero] at hc
    exact hc.symm
  have hs : Function.Surjective g := by
    intro b
    obtain ⟨a, ha⟩ := (ex₁ b.val).mp b.property
    exact ⟨a, Subtype.ext ha⟩
  exact (cohomologyIso (X := X) (constantKernelIso k d) 2).trans
    (AddEquiv.ofBijective g ⟨hi, hs⟩)

section PID

variable (K : Type) [Field K] [IsAlgClosed K]
variable (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra K R]
variable (d : ℕ) [NeZero (d : K)]

/-- For affine PID charts this degree-two identification has no cohomology
hypothesis. It uses the verified native Pic vanishing and actual Kummer maps. -/
def pidCyclicEquivUnitsTorsion :
    Sheaf.H (constant (spectrum R) (ZMod d)) 2 ≃+ unitsTorsion (spectrum R) d := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let u : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let v : ULift.{1} (Additive (rootsOfUnity d K)) ≃+ ULift.{1} (ZMod d) :=
    AddEquiv.ulift.trans (u.trans AddEquiv.ulift.symm)
  let i : coefficientGroup K d ≅ AddCommGrpCat.of (ULift.{1} (ZMod d)) := v.toAddCommGrpIso
  let q := (constantSheaf (J (spectrum R)) G).mapIso i
  let e := cohomologyIso (X := spectrum R) q 2
  let k : spectrum R ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K R))
  exact e.symm.trans (rootsEquivUnitsTorsion k d (ProetalePIDUnitHOne.HOne_subsingleton R))

end PID

end
end ManuscriptAudit.ProetaleKummerHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerHTwo.mem_unitsTorsion,
      ``ManuscriptAudit.ProetaleKummerHTwo.rootsEquivUnitsTorsion,
      ``ManuscriptAudit.ProetaleKummerHTwo.pidCyclicEquivUnitsTorsion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
