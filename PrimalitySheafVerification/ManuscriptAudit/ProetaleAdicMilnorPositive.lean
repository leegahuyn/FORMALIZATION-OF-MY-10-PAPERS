import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicProductPositiveCoordinates
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicReductionAllDegrees

/-! The actual continuous adic comparison surjects in positive degrees.
Onto preceding finite transitions give the corresponding degree's uniqueness. -/

namespace ManuscriptAudit.ProetaleAdicMilnorPositive

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleAdicNativeExactSequence (sequence)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueSheaf residueReduction residueTransition)
open ProetaleAdicProductPositiveCoordinates (projection coordinates coordinates_bijective)
open ProetaleAdicReductionAllDegrees (nativeCompatible nativeStep reductionMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ)

private abbrev Q := sequence X ℓ
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

private abbrev t (n : ℕ) := (lift X).map (residueTransition X ℓ n)
private abbrev r (n : ℕ) := (lift X).map (residueReduction X ℓ n)

private theorem difference_comp_projection (n : ℕ) :
    (Q X ℓ).g ≫ projection X ℓ n =
      projection X ℓ n - projection X ℓ (n+1) ≫ t X ℓ n := by
  change (lift X).map (ProetaleAdicProductKernel.difference X ℓ) ≫
      (lift X).map (Pi.π (residueSheaf X ℓ) n) = _
  rw [← (lift X).map_comp, ProetaleAdicProductKernel.difference_π,
    (lift X).map_sub, (lift X).map_comp]

private theorem inclusion_comp_projection (n : ℕ) :
    (Q X ℓ).f ≫ projection X ℓ n = r X ℓ n := by
  change (lift X).map (ProetaleAdicProductKernel.inclusion X ℓ) ≫
      (lift X).map (Pi.π (residueSheaf X ℓ) n) = _
  rw [← (lift X).map_comp, ProetaleAdicProductKernel.inclusion_π]

private theorem coordinate_difference (z : Sheaf.H (Q X ℓ).X₂ (d+1)) (n : ℕ) :
    coordinates X ℓ d (Sheaf.H.map (Q X ℓ).g (d+1) z) n =
      coordinates X ℓ d z n - nativeStep X ℓ (d+1) n (coordinates X ℓ d z (n+1)) := by
  let p := projection X ℓ n
  let q := projection X ℓ (n+1) ≫ t X ℓ n
  let P := (Q X ℓ).X₂
  let F := finiteCoefficient X ℓ n
  have hm : (Ext.mk₀ (p - q) : Ext.{1} P F 0) = Ext.mk₀ p - Ext.mk₀ q :=
    map_sub (Ext.addEquiv₀ (X := P) (Y := F)).symm p q
  have hd : Sheaf.H.map (p-q) (d+1) z = Sheaf.H.map p (d+1) z - Sheaf.H.map q (d+1) z := by
    change z.comp (Ext.mk₀ (p-q)) (add_zero (d+1)) =
      z.comp (Ext.mk₀ p) (add_zero (d+1)) - z.comp (Ext.mk₀ q) (add_zero (d+1))
    rw [hm]
    exact map_sub (z.precomp F (add_zero (d+1))) _ _
  calc
    _ = Sheaf.H.map ((Q X ℓ).g ≫ p) (d+1) z := (Sheaf.H.map_comp_apply _ _ _).symm
    _ = Sheaf.H.map (p-q) (d+1) z :=
      congrArg (fun f => Sheaf.H.map f (d+1) z) (difference_comp_projection X ℓ n)
    _ = Sheaf.H.map p (d+1) z - Sheaf.H.map q (d+1) z := hd
    _ = _ := congrArg (fun x => Sheaf.H.map p (d+1) z - x)
      (Sheaf.H.map_comp_apply (projection X ℓ (n+1)) (t X ℓ n) z)

/-- Surjectivity holds for the actual continuous integral coefficient on every native base. -/
theorem reduction_surjective : Function.Surjective (reductionMap X ℓ (d+1)) := by
  intro x
  obtain ⟨z, hz⟩ := (coordinates_bijective X ℓ d).surjective x.val
  have hd : Sheaf.H.map (Q X ℓ).g (d+1) z = 0 := by
    apply (coordinates_bijective X ℓ d).injective
    rw [map_zero]
    funext n
    rw [coordinate_difference, congrFun hz n, congrFun hz (n+1), x.property n]
    exact sub_self _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ (integers X)
    (ProetaleAdicNativeExactSequence.shortExact X ℓ) z hd
  refine ⟨a, Subtype.ext (funext fun n => ?_)⟩
  change Sheaf.H.map (r X ℓ n) (d+1) a = x.val n
  change Sheaf.H.map (Q X ℓ).f (d+1) a = z at ha
  calc
    _ = Sheaf.H.map ((Q X ℓ).f ≫ projection X ℓ n) (d+1) a :=
      congrArg (fun g => Sheaf.H.map g (d+1) a) (inclusion_comp_projection X ℓ n).symm
    _ = coordinates X ℓ d (Sheaf.H.map (Q X ℓ).f (d+1) a) n :=
      Sheaf.H.map_comp_apply (Q X ℓ).f (projection X ℓ n) a
    _ = _ := (congrArg (fun y => coordinates X ℓ d y n) ha).trans (congrFun hz n)



/-- Onto finite transition homomorphisms in a positive degree make the derived
difference map on the corresponding countable product onto. -/
theorem product_difference_surjective
    (hs : ∀ n, Function.Surjective (nativeStep X ℓ (d+1) n)) :
    Function.Surjective (Sheaf.H.map (Q X ℓ).g (d+1)) := by
  classical
  intro z
  let y := coordinates X ℓ d z
  have hl (n : ℕ) (u : Sheaf.H (finiteCoefficient X ℓ n) (d+1)) :
      ∃ x, nativeStep X ℓ (d+1) n x = u := hs n u
  choose next hnext using hl
  let x : ∀ n, Sheaf.H (finiteCoefficient X ℓ n) (d+1) :=
    Nat.rec 0 (fun n xₙ => next n (xₙ - y n))
  have hx (n : ℕ) : x n - nativeStep X ℓ (d+1) n (x (n+1)) = y n := by
    rw [show x (n+1) = next n (x n - y n) from rfl, hnext]
    exact sub_sub_cancel _ _
  obtain ⟨w, hw⟩ := (coordinates_bijective X ℓ d).surjective x
  refine ⟨w, (coordinates_bijective X ℓ d).injective ?_⟩
  funext n
  rw [coordinate_difference, congrFun hw n, congrFun hw (n+1)]
  exact hx n

private theorem inclusion_injective
    (hs : ∀ n, Function.Surjective (nativeStep X ℓ (d+1) n)) :
    Function.Injective (Sheaf.H.map (Q X ℓ).f (d+2)) := by
  let S := Q X ℓ
  have hS : S.ShortExact := ProetaleAdicNativeExactSequence.shortExact X ℓ
  intro a b hab
  apply sub_eq_zero.mp
  have hz : Sheaf.H.map S.f (d+2) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (X := _) hS (a-b) hz
    (show d+1+1 = d+2 by rfl)
  obtain ⟨x, hx⟩ := product_difference_surjective X ℓ d hs y
  rw [← hy, ← hx]
  change (x.comp (Ext.mk₀ S.g) (add_zero (d+1))).comp hS.extClass rfl = 0
  simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- Surjectivity of the preceding residue transitions gives unique lifts in
the actual continuous cohomology of the next degree. -/
theorem reduction_injective
    (hs : ∀ n, Function.Surjective (nativeStep X ℓ (d+1) n)) :
    Function.Injective (reductionMap X ℓ (d+2)) := by
  intro a b hab
  apply inclusion_injective X ℓ d hs
  apply (coordinates_bijective X ℓ (d+1)).injective
  funext n
  have h (z : Sheaf.H (Q X ℓ).X₁ (d+2)) :
      coordinates X ℓ (d+1) (Sheaf.H.map (Q X ℓ).f (d+2) z) n =
        (reductionMap X ℓ (d+2) z).val n := by
    let p := projection X ℓ n
    calc
      _ = Sheaf.H.map ((Q X ℓ).f ≫ p) (d+2) z := (Sheaf.H.map_comp_apply (Q X ℓ).f p z).symm
      _ = _ := congrArg (fun f => Sheaf.H.map f (d+2) z) (inclusion_comp_projection X ℓ n)
  rw [h a, h b, hab]

def reductionEquiv
    (hs : ∀ n, Function.Surjective (nativeStep X ℓ (d+1) n)) :
    X.EllAdicCohomology ℓ (d+2) ≃+ nativeCompatible X ℓ (d+2) :=
  AddEquiv.ofBijective (reductionMap X ℓ (d+2))
    ⟨reduction_injective X ℓ d hs, reduction_surjective X ℓ (d+1)⟩

end
end ManuscriptAudit.ProetaleAdicMilnorPositive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicMilnorPositive.reduction_surjective,
      ``ManuscriptAudit.ProetaleAdicMilnorPositive.product_difference_surjective,
      ``ManuscriptAudit.ProetaleAdicMilnorPositive.reduction_injective,
      ``ManuscriptAudit.ProetaleAdicMilnorPositive.reductionEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
