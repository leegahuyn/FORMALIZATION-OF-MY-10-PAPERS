import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerBoundaryTransition
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerCyclicCoordinates
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicReductionAllDegrees

/-! On any native site with vanishing units H¹, actual reduction is
surjective in finite-coefficient H¹. The same unit lifts every label. -/

namespace ManuscriptAudit.ProetaleKummerResidueHOneTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleDiscreteConstant (nativeResidueIso nativeResidueIso_naturality)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerCyclicCoordinates (cyclicIso reduction cyclicIso_naturality)
open ProetaleKummerConstantTransition (coefficientTransition)
open ProetaleKummerSheafTransition (constantTransition)
open ProetaleKummerBoundaryNative (unitBoundary unitBoundary_surjective)
open ProetaleKummerBoundaryTransition (unitBoundary_transition)
open ProetaleUnitSheaf (unitSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
  (k : X ⟶ Spec (CommRingCat.of K)) (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev F := constantSheaf (Scheme.ProEt.topology X) A

local instance modulus_neZero (n : ℕ) : NeZero (l ^ n) :=
  ⟨pow_ne_zero n (show l.Prime from Fact.out).ne_zero⟩

local instance cast_modulus_neZero (n : ℕ) : NeZero ((l ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩

private abbrev step (n : ℕ) :=
  (ProetaleCoefficientUniverseLift.lift X).map (ProetaleResidueSheaves.residueTransition X l n)

private def modelIso (n : ℕ) :
    (F (X := X)).obj (coefficientGroup K (l ^ n)) ≅ finiteCoefficient X l n :=
  ((F (X := X)).mapIso (cyclicIso K l n)).symm ≪≫ nativeResidueIso X l n

private theorem inverse_cyclic_natural (n : ℕ) :
    coefficientTransition K l n ≫ (cyclicIso K l n).inv =
      (cyclicIso K l (n + 1)).inv ≫ reduction l n := by
  let e := cyclicIso K l (n + 1)
  let j := cyclicIso K l n
  apply (cancel_epi e.hom).mp
  calc
    _ = (e.hom ≫ coefficientTransition K l n) ≫ j.inv := (Category.assoc _ _ _).symm
    _ = (reduction l n ≫ j.hom) ≫ j.inv :=
      congrArg (fun a ↦ a ≫ j.inv) (cyclicIso_naturality K l n)
    _ = reduction l n := by rw [Category.assoc, j.hom_inv_id, Category.comp_id]
    _ = _ := (e.hom_inv_id_assoc _).symm

set_option maxHeartbeats 4000000 in
private theorem model_natural (n : ℕ) :
    constantTransition (K := K) (X := X) l n ≫ (modelIso (K := K) (X := X) l n).hom =
      (modelIso (K := K) (X := X) l (n + 1)).hom ≫ step (X := X) l n := by
  let C := F (X := X)
  let β := nativeResidueIso X l n
  let γ := nativeResidueIso X l (n + 1)
  let en := (cyclicIso K l n).inv
  let es := (cyclicIso K l (n + 1)).inv
  change C.map (coefficientTransition K l n) ≫ C.map en ≫ β.hom =
    (C.map es ≫ γ.hom) ≫ step (X := X) l n
  calc
    _ = C.map (coefficientTransition K l n ≫ en) ≫ β.hom := by rw [C.map_comp, Category.assoc]
    _ = C.map (es ≫ reduction l n) ≫ β.hom :=
      congrArg (fun a ↦ C.map a ≫ β.hom) (inverse_cyclic_natural (K := K) l n)
    _ = C.map es ≫ C.map (reduction l n) ≫ β.hom := by rw [C.map_comp, Category.assoc]
    _ = C.map es ≫ γ.hom ≫ step (X := X) l n :=
      congrArg (fun a ↦ C.map es ≫ a) (nativeResidueIso_naturality X l n)
    _ = _ := (Category.assoc _ _ _).symm

/-- A unit's actual native cyclic Kummer class. -/
def residueBoundary (n : ℕ) :
    Sheaf.H (unitSheaf X) 0 →+ Sheaf.H (finiteCoefficient X l n) 1 :=
  (cohomologyIso (modelIso (K := K) (X := X) l n) 1).toAddMonoidHom.comp
    (unitBoundary k (l ^ n))

/-- The same unit gives the original transition on actual native cohomology. -/
theorem boundary_natural (n : ℕ) (x : Sheaf.H (unitSheaf X) 0) :
    nativeStep X l 1 n (residueBoundary k l (n + 1) x) = residueBoundary k l n x := by
  let a := unitBoundary k (l ^ (n + 1)) x
  let hi := (modelIso (K := K) (X := X) l n).hom
  let hj := (modelIso (K := K) (X := X) l (n + 1)).hom
  change Sheaf.H.map (step (X := X) l n) 1 (Sheaf.H.map hj 1 a) =
    Sheaf.H.map hi 1 (unitBoundary k (l ^ n) x)
  rw [← Sheaf.H.map_comp_apply, ← model_natural (K := K) (X := X) l n, Sheaf.H.map_comp_apply,
    unitBoundary_transition k l n]

set_option maxHeartbeats 4800000 in
include k in
/-- Surjectivity uses the literal residue transitions in the native site. -/
theorem step_surjective (hUnits : Subsingleton (Sheaf.H (unitSheaf X) 1)) (n : ℕ) :
    Function.Surjective (nativeStep X l 1 n) := by
  let e : Sheaf.H ((F (X := X)).obj (coefficientGroup K (l ^ n))) 1 ≃+
      Sheaf.H (finiteCoefficient X l n) 1 :=
    cohomologyIso (modelIso (K := K) (X := X) l n) 1
  have h : Function.Surjective (residueBoundary k l n) :=
    e.surjective.comp (unitBoundary_surjective k (l ^ n) hUnits)
  intro x
  obtain ⟨u, hu⟩ := h x
  exact ⟨residueBoundary k l (n + 1) u, (boundary_natural k l n u).trans hu⟩

end
end ManuscriptAudit.ProetaleKummerResidueHOneTransition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerResidueHOneTransition.boundary_natural,
      ``ManuscriptAudit.ProetaleKummerResidueHOneTransition.step_surjective] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
