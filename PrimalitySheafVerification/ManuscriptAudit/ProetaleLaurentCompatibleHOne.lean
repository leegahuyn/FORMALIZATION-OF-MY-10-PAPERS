import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerBoundaryTransition
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerCyclicCoordinates
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentCyclicHOne

/-! Native Kummer classes of the Laurent exponents give coherent
finite degree-one groups for the actual residue reductions. -/

namespace ManuscriptAudit.ProetaleLaurentCompatibleHOne

open AlgebraicGeometry CategoryTheory
open ProetaleKummerPower (J G)
open ProetaleKummerCyclicCoordinates (cyclicIso cyclicIso_naturality reduction)
open ProetaleKummerSheafTransition (constantTransition)
open ProetaleKummerBoundaryTransition (unitBoundary_transition)
open ProetaleLaurentCyclicHOne (cyclicToRootsHOne cyclicToRootsHOne_intCast exponentUnit)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

abbrev laurent := Spec (CommRingCat.of (LaurentPolynomial K))

private abbrev structureMap : laurent K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (LaurentPolynomial K)))

local instance pow_neZero (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩

local instance cast_pow_neZero (n : ℕ) : NeZero ((ℓ ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩

private abbrev F := constantSheaf (J (laurent K)) G

abbrev transition (n : ℕ) := (F K).map (reduction ℓ n)

private abbrev coefficientIso (n : ℕ) := (F K).mapIso (cyclicIso K ℓ n)

private abbrev coefficientEquiv (n : ℕ) := cohomologyIso (X := laurent K) (coefficientIso K ℓ n) 1

/-- Laurent exponents with one coherent root choice at all genuine residue levels. -/
def cyclicToHOne (n : ℕ) :
    ZMod (ℓ ^ n) ≃+ Sheaf.H (constant (laurent K) (ZMod (ℓ ^ n))) 1 :=
  (cyclicToRootsHOne K (ℓ ^ n)).trans (coefficientEquiv K ℓ n).symm

private theorem roots_coherence (n : ℕ) (a : ZMod (ℓ ^ (n + 1))) :
    Sheaf.H.map (constantTransition (K := K) (X := laurent K) ℓ n) 1
        (cyclicToRootsHOne K (ℓ ^ (n + 1)) a) =
      cyclicToRootsHOne K (ℓ ^ n) (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  simp only [map_intCast, cyclicToRootsHOne_intCast]
  exact unitBoundary_transition (structureMap K) ℓ n (exponentUnit K z)

set_option maxHeartbeats 1400000 in
/-- The actual native transition maps are the actual exponent reductions. -/
theorem cyclicToHOne_naturality (n : ℕ) (a : ZMod (ℓ ^ (n + 1))) :
    Sheaf.H.map (transition K ℓ n) 1 (cyclicToHOne K ℓ (n + 1) a) =
      cyclicToHOne K ℓ n (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a) := by
  let f := transition K ℓ n
  let g := constantTransition (K := K) (X := laurent K) ℓ n
  let e := (coefficientIso K ℓ n).hom
  let t := (coefficientIso K ℓ (n + 1)).hom
  let x := cyclicToHOne K ℓ (n + 1) a
  have h : f ≫ e = t ≫ g := by
    change (F K).map (reduction ℓ n) ≫ (F K).map (cyclicIso K ℓ n).hom =
      (F K).map (cyclicIso K ℓ (n + 1)).hom ≫
        (F K).map (ProetaleKummerConstantTransition.coefficientTransition K ℓ n)
    simp only [← Functor.map_comp]
    exact congrArg (F K).map (cyclicIso_naturality K ℓ n).symm
  have hx : coefficientEquiv K ℓ (n + 1) x = cyclicToRootsHOne K (ℓ ^ (n + 1)) a :=
    (coefficientEquiv K ℓ (n + 1)).apply_symm_apply _
  apply (coefficientEquiv K ℓ n).injective
  calc
    _ = Sheaf.H.map (f ≫ e) 1 x := (Sheaf.H.map_comp_apply f e x).symm
    _ = Sheaf.H.map (t ≫ g) 1 x := congrArg (fun m ↦ Sheaf.H.map m 1 x) h
    _ = Sheaf.H.map g 1 (coefficientEquiv K ℓ (n + 1) x) := Sheaf.H.map_comp_apply t g x
    _ = Sheaf.H.map g 1 (cyclicToRootsHOne K (ℓ ^ (n + 1)) a) := by rw [hx]
    _ = cyclicToRootsHOne K (ℓ ^ n) (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a) :=
      roots_coherence K ℓ n a
    _ = _ := ((coefficientEquiv K ℓ n).apply_symm_apply _).symm

end
end ManuscriptAudit.ProetaleLaurentCompatibleHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleLaurentCompatibleHOne.cyclicToHOne_naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
