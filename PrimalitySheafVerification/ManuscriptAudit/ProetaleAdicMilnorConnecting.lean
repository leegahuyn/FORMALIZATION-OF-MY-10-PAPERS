import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicMilnorPositive

/-! The first derived inverse-limit obstruction for actual continuous
pro-étale cohomology is the cokernel of the literal consecutive difference. -/

namespace ManuscriptAudit.ProetaleAdicMilnorConnecting

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleAdicNativeExactSequence (sequence shortExact)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees
open ProetaleAdicProductPositiveCoordinates
open ProetaleAdicMilnorPositive (coordinate_difference inclusion_comp_projection)
open ProetaleCoefficientUniverseLift (lift)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ)

private abbrev S := sequence X ℓ
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

abbrev Tuples := ∀ n, Sheaf.H (finiteCoefficient X ℓ n) (d+1)

/-- The actual countable difference in finite positive-degree groups. -/
def differenceTuples : Tuples X ℓ d →+ Tuples X ℓ d where
  toFun u n := u n - nativeStep X ℓ (d+1) n (u (n+1))
  map_zero' := by
    funext n
    simp
  map_add' u v := by
    funext n
    change u n + v n - nativeStep X ℓ (d+1) n (u (n+1) + v (n+1)) =
      (u n - nativeStep X ℓ (d+1) n (u (n+1))) +
        (v n - nativeStep X ℓ (d+1) n (v (n+1)))
    rw [map_add]
    abel

private abbrev E := coordinateEquiv X ℓ d

/-- The connecting homomorphism on actual product coordinates. -/
def connecting : Tuples X ℓ d →+ X.EllAdicCohomology ℓ (d+2) :=
  ((shortExact X ℓ).extClass.postcomp (integers X) (show d+1+1 = d+2 by rfl)).comp
    (E X ℓ d).symm.toAddMonoidHom

private theorem difference_coordinates (z : Sheaf.H (S X ℓ).X₂ (d+1)) :
    differenceTuples X ℓ d (E X ℓ d z) =
      E X ℓ d (Sheaf.H.map (S X ℓ).g (d+1) z) := by
  funext n
  exact (coordinate_difference X ℓ d z n).symm


/-- The kernel of the connecting map is the image of the genuine difference on
the product of finite cohomology groups. -/
theorem connecting_kernel :
    (connecting X ℓ d).ker = (differenceTuples X ℓ d).range := by
  ext u
  constructor
  · intro hu
    let z := (E X ℓ d).symm u
    have hz : z.comp (shortExact X ℓ).extClass (show d+1+1 = d+2 by rfl) = 0 := hu
    obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ (integers X) (shortExact X ℓ) z
      (show d+1+1 = d+2 by rfl) hz
    refine ⟨E X ℓ d w, ?_⟩
    calc
      _ = E X ℓ d (Sheaf.H.map (S X ℓ).g (d+1) w) := difference_coordinates X ℓ d w
      _ = E X ℓ d z := congrArg (E X ℓ d) hw
      _ = u := (E X ℓ d).apply_symm_apply u
  · rintro ⟨v, rfl⟩
    let w := (E X ℓ d).symm v
    have hV : E X ℓ d w = v := (E X ℓ d).apply_symm_apply v
    change connecting X ℓ d (differenceTuples X ℓ d v) = 0
    rw [← hV, difference_coordinates]
    change ((E X ℓ d).symm (E X ℓ d (Sheaf.H.map (S X ℓ).g (d+1) w))).comp
      (shortExact X ℓ).extClass (show d+1+1 = d+2 by rfl) = 0
    rw [AddEquiv.symm_apply_apply]
    change (w.comp (Ext.mk₀ (S X ℓ).g) (add_zero (d+1))).comp (shortExact X ℓ).extClass rfl = 0
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

private theorem reduction_coordinate (a : X.EllAdicCohomology ℓ (d+2)) (n : ℕ) :
    (reductionMap X ℓ (d+2) a).val n =
      coordinates X ℓ (d+1) (Sheaf.H.map (S X ℓ).f (d+2) a) n := by
  let f := (S X ℓ).f
  let p := projection X ℓ n
  let r := (lift X).map (ProetaleResidueSheaves.residueReduction X ℓ n)
  change Sheaf.H.map r (d+2) a = Sheaf.H.map p (d+2) (Sheaf.H.map f (d+2) a)
  calc
    _ = Sheaf.H.map (f ≫ p) (d+2) a :=
      congrArg (fun g => Sheaf.H.map g (d+2) a) (inclusion_comp_projection X ℓ n).symm
    _ = _ := Sheaf.H.map_comp_apply f p a


/-- The genuine derived inverse-limit obstruction is precisely the kernel of
the native reduction into the compatible finite groups. -/
theorem connecting_range :
    (connecting X ℓ d).range = (reductionMap X ℓ (d+2)).ker := by
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    have hf : Sheaf.H.map (S X ℓ).f (d+2) (connecting X ℓ d y) = 0 := by
      change (((E X ℓ d).symm y).comp (shortExact X ℓ).extClass rfl).comp
        (Ext.mk₀ (S X ℓ).f) (add_zero (d+2)) = 0
      simp only [Ext.comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]
    change reductionMap X ℓ (d+2) (connecting X ℓ d y) = 0
    apply Subtype.ext
    funext n
    change (reductionMap X ℓ (d+2) (connecting X ℓ d y)).val n = 0
    simp only [reduction_coordinate, hf, map_zero, Pi.zero_apply]
  · intro ha
    change reductionMap X ℓ (d+2) a = 0 at ha
    have hf : Sheaf.H.map (S X ℓ).f (d+2) a = 0 := by
      apply (coordinates_bijective X ℓ (d+1)).injective
      rw [map_zero]
      funext n
      change coordinates X ℓ (d+1) (Sheaf.H.map (S X ℓ).f (d+2) a) n = 0
      rw [← reduction_coordinate X ℓ d]
      exact congrArg (fun v : nativeCompatible X ℓ (d+2) => v.val n) ha
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (X := integers X) (shortExact X ℓ) a hf
      (show d+1+1 = d+2 by rfl)
    refine ⟨E X ℓ d z, ?_⟩
    change ((E X ℓ d).symm (E X ℓ d z)).comp (shortExact X ℓ).extClass rfl = a
    rw [AddEquiv.symm_apply_apply]
    exact hz

end
end ManuscriptAudit.ProetaleAdicMilnorConnecting

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicMilnorConnecting.connecting_kernel,
      ``ManuscriptAudit.ProetaleAdicMilnorConnecting.connecting_range] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
