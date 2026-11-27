import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.CuspPicard
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSequence
import PrimalitySheafVerification.ManuscriptAudit.ProetalePIDUnitHOne

/-! The actual affine line has zero native pro-étale degree-one
cohomology for every invertible finite cyclic coefficient group. -/

namespace ManuscriptAudit.ProetaleAffineLineCyclicHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum terminal)
open ProetaleUnitSheaf (unitSheaf specUnits)
open ProetaleKummerPower (J G power power_eval)
open ProetaleKummerSequence (sequence sequence_shortExact constantKernelIso)
open ProetaleKummerCoefficientMap (coefficientGroup)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra K A]

private abbrev toField : spectrum A ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K A))

private abbrev hT : IsTerminal (terminal A) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale (spectrum A)

/-- Degree zero of the actual native units sheaf computes coordinate units. -/
def unitsHZeroEquiv : Sheaf.H (unitSheaf (spectrum A)) 0 ≃+ Additive Aˣ :=
  (Sheaf.H.equiv₀ _ (hT A)).trans (specUnits (CommRingCat.of A) (𝟙 (spectrum A)))

theorem unitsHZeroEquiv_power (d : ℕ) (x : Sheaf.H (unitSheaf (spectrum A)) 0) :
    unitsHZeroEquiv A (Sheaf.H.map (power (spectrum A) d) 0 x) =
      d • unitsHZeroEquiv A x := by
  let e := specUnits (CommRingCat.of A) (𝟙 (spectrum A))
  change e ((Sheaf.H.equiv₀ _ (hT A)) (Sheaf.H.map (power (spectrum A) d) 0 x)) =
    d • e ((Sheaf.H.equiv₀ _ (hT A)) x)
  rw [← Sheaf.H.equiv₀_naturality, power_eval, map_nsmul]

variable [IsDomain A] [IsPrincipalIdealRing A]

/-- Over a PID, surjectivity of coordinate powers kills degree-one
native pro-étale cohomology of coefficient roots. -/
theorem roots_HOne_subsingleton (d : ℕ) [NeZero d] [NeZero (d : K)]
    [HasEnoughRootsOfUnity K d]
    (hs : ∀ y : Aˣ, ∃ x : Aˣ, x ^ d = y) :
    Subsingleton (Sheaf.H ((constantSheaf (J (spectrum A)) G).obj (coefficientGroup K d)) 1) := by
  let X := spectrum A
  let Z := (constantSheaf (J X) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  let h := sequence_shortExact (toField (K := K) A) d
  have h₀ := Ext.covariant_sequence_exact₃' Z h 0 1 rfl
  have h₁ := Ext.covariant_sequence_exact₁' Z h 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h₀ h₁
  let δ : Sheaf.H (unitSheaf X) 0 →+ Sheaf.H (kernel (power X d)) 1 :=
    h.extClass.postcomp Z (show 0 + 1 = 1 by rfl)
  have h₀' : Function.Exact (Sheaf.H.map (power X d) 0) δ := h₀
  have h₁' : Function.Exact δ (Sheaf.H.map (kernel.ι (power X d)) 1) := h₁
  let r := ProetaleCohomologyIso.cohomologyIso (X := X)
    (constantKernelIso (toField (K := K) A) d) 1
  have hUn := ProetalePIDUnitHOne.HOne_subsingleton A
  refine subsingleton_of_forall_eq 0 (fun a ↦ ?_)
  have hz : Sheaf.H.map (kernel.ι (power X d)) 1 (r a) = 0 := hUn.elim _ _
  obtain ⟨y, hy⟩ := (h₁' (r a)).mp hz
  obtain ⟨u, hu⟩ := hs (unitsHZeroEquiv A y).toMul
  let x := (unitsHZeroEquiv A).symm (Additive.ofMul u)
  have hx : Sheaf.H.map (power X d) 0 x = y := by
    apply (unitsHZeroEquiv A).injective
    rw [unitsHZeroEquiv_power, AddEquiv.apply_symm_apply]
    change Additive.ofMul (u ^ d) = unitsHZeroEquiv A y
    rw [hu]
    rfl
  have hy₀ : δ y = 0 := (h₀' y).mpr ⟨x, hx⟩
  apply r.injective
  rw [map_zero, ← hy, hy₀]

variable (K) [IsAlgClosed K]

/-- Native pro-étale degree-one cohomology of the actual affine line
vanishes for every positive cyclic coefficient order invertible in K. -/
theorem affineLine_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (J (spectrum (Polynomial K))) G).obj
      (AddCommGrpCat.of (ULift.{1} (ZMod d)))) 1) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let u : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let v : ULift.{1} (Additive (rootsOfUnity d K)) ≃+ ULift.{1} (ZMod d) :=
    AddEquiv.ulift.trans (u.trans AddEquiv.ulift.symm)
  let L := J (spectrum (Polynomial K))
  let i : coefficientGroup K d ≅ AddCommGrpCat.of (ULift.{1} (ZMod d)) := v.toAddCommGrpIso
  let q := (constantSheaf L G).mapIso i
  let e := ProetaleCohomologyIso.cohomologyIso (X := spectrum (Polynomial K)) q 1
  have h := roots_HOne_subsingleton (K := K) (Polynomial K) d
    (CuspPicard.paper2_polynomial_unit_power_surjective K d (Nat.pos_of_ne_zero (NeZero.ne d)))
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

end
end ManuscriptAudit.ProetaleAffineLineCyclicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineLineCyclicHOne.unitsHZeroEquiv_power,
      ``ManuscriptAudit.ProetaleAffineLineCyclicHOne.roots_HOne_subsingleton,
      ``ManuscriptAudit.ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
