import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.PIDTwistedDescentUnits
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTensorFaces
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitSheaf

/-! A unit cocycle on an affine faithfully flat cover of a PID spectrum
has a primitive in the actual pro-étale units sheaf. -/

namespace ManuscriptAudit.ProetaleUnitCech

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor ProetaleTensorFaces
open ProetaleUnitSheaf (unitSheaf specUnits)
open TwistedTensorEqualizer (Double Triple first second face01 face02 face12 IsCocycle)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A]

abbrev F := unitSheaf (spectrum A)

private abbrev unitsAt (R : Type) [CommRing R] [Algebra A R]
    [WeaklyEtale (structureMap A R)] :
    (F A).obj.obj (op (object A R)) ≃+ Additive Rˣ :=
  specUnits (CommRingCat.of R) (structureMap A R)

theorem unitsAt_natural {R T : Type} [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]
    [WeaklyEtale (structureMap A R)] [WeaklyEtale (structureMap A T)]
    (g : R →ₐ[A] T) (s : (F A).obj.obj (op (object A R))) :
    unitsAt A T ((F A).obj.map (arrow A g).op s) =
      Additive.ofMul (Units.map g.toRingHom.toMonoidHom (unitsAt A R s).toMul) := by
  let f := CommRingCat.ofHom g.toRingHom
  have h : ringUnits.map (Spec.map f).appTop ≫ (ringUnits.mapIso (Scheme.ΓSpecIso _)).hom =
      (ringUnits.mapIso (Scheme.ΓSpecIso _)).hom ≫ ringUnits.map f := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  exact ConcreteCategory.congr_hom h s.down

variable [IsDomain A] [IsPrincipalIdealRing A]
variable (B : Type) [CommRing B] [Nontrivial B] [Algebra A B]
  [WeaklyEtale (structureMap A B)] [Module.FaithfullyFlat A B]

/-- Every actual unit cocycle on this affine cover is a coboundary, by
the faithfully flat twisted rank-one module over the PID. -/
theorem exists_primitive (b : (F A).obj.obj (op (object A (Double A B))))
    (hb : (F A).obj.map (e₁₂ A B).op b - (F A).obj.map (e₀₂ A B).op b +
      (F A).obj.map (e₀₁ A B).op b = 0) :
    ∃ a : (F A).obj.obj (op (object A B)),
      b = (F A).obj.map (p₁ A B).op a - (F A).obj.map (p₀ A B).op a := by
  let t := (unitsAt A (Double A B) b).toMul
  have ht : IsCocycle A B t := by
    have he : (F A).obj.map (e₀₂ A B).op b =
        (F A).obj.map (e₁₂ A B).op b + (F A).obj.map (e₀₁ A B).op b := by
      apply sub_eq_zero.mp
      calc
        _ = -((F A).obj.map (e₁₂ A B).op b - (F A).obj.map (e₀₂ A B).op b +
              (F A).obj.map (e₀₁ A B).op b) := by abel
        _ = 0 := by rw [hb, neg_zero]
    have he' := congrArg (unitsAt A (Triple A B)) he
    rw [map_add] at he'
    change unitsAt A _ ((F A).obj.map (arrow A (face02 A B)).op b) =
      unitsAt A _ ((F A).obj.map (arrow A (face12 A B)).op b) +
        unitsAt A _ ((F A).obj.map (arrow A (face01 A B)).op b) at he'
    rw [unitsAt_natural, unitsAt_natural, unitsAt_natural] at he'
    exact congrArg (fun s : Additive (Triple A B)ˣ ↦ (s.toMul : Triple A B)) he'
  obtain ⟨v, hv⟩ := PIDTwistedDescentUnits.exists_coboundary A B t ht
  let a := (unitsAt A B).symm (Additive.ofMul v)
  refine ⟨a, (unitsAt A (Double A B)).injective ?_⟩
  rw [map_sub]
  change unitsAt A _ b = unitsAt A _ ((F A).obj.map (arrow A (second A B)).op a) -
    unitsAt A _ ((F A).obj.map (arrow A (first A B)).op a)
  rw [unitsAt_natural, unitsAt_natural]
  change _ = Additive.ofMul (Units.map (second A B).toRingHom.toMonoidHom
      (((unitsAt A B) ((unitsAt A B).symm (Additive.ofMul v))).toMul)) -
    Additive.ofMul (Units.map (first A B).toRingHom.toMonoidHom
      (((unitsAt A B) ((unitsAt A B).symm (Additive.ofMul v))).toMul))
  rw [AddEquiv.apply_symm_apply]
  apply Additive.ext
  apply Units.ext
  change (t : Double A B) = second A B (v : B) * first A B (↑(v⁻¹) : B)
  exact hv

end
end ManuscriptAudit.ProetaleUnitCech

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleUnitCech.unitsAt_natural,
      ``ManuscriptAudit.ProetaleUnitCech.exists_primitive] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
