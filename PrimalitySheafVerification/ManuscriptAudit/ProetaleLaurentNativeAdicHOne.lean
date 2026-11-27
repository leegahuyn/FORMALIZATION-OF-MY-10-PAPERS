import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LaurentKummerGeneratorLifts
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentAdicCoordinates
import PrimalitySheafVerification.ManuscriptAudit.SheafSimultaneousExtensionEpi

/-! The actual native integral Laurent group in degree one is the adic
integer group. A single genuine all-root cover gives the simultaneous lifting. -/

namespace ManuscriptAudit.ProetaleLaurentNativeAdicHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open LaurentKummerTowerCover (covering coverArrow)
open LaurentKummerGeneratorLifts (unitMap terminalIsTerminal)
open ProetaleLaurentCompatibleHOne (laurent)
open ProetaleLaurentAdicCoordinates (levelEquiv compatibleEquiv compatibleEquiv_apply)
open ProetaleAdicHOneDetection (finiteCoefficient compatibleHOne reductionMap reductionMap_injective
  exists_lift_of_actual_product_class)
open ProetaleKummerPower (J G)
open ProetaleKummerSequence (sequence sequence_shortExact constantKernelIso)
open ProetaleKummerKernelTransition (kernelBoundary)
open ProetaleKummerCyclicCoordinates (cyclicIso)
open ProetaleKummerBoundaryNative (unitBoundary)
open ProetaleLaurentCyclicHOne (exponentUnit cyclicToRootsHOne cyclicToRootsHOne_intCast)
open ProetaleDiscreteConstant (nativeResidueIso)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := laurent K
private abbrev k : X K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (LaurentPolynomial K)))

local instance pow_neZero (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩

local instance cast_pow_neZero (n : ℕ) : NeZero ((ℓ ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩

private abbrev S (n : ℕ) := ProetaleKummerSequence.sequence (X K) (ℓ ^ n)

private abbrev digit (a : ℤ_[ℓ]) (n : ℕ) := (PadicInt.toZModPow n a).val

private abbrev u (a : ℤ_[ℓ]) (n : ℕ) := unitMap K (digit ℓ a n)

private abbrev kernelResidueIso (n : ℕ) : (S K ℓ n).X₁ ≅ finiteCoefficient (X K) ℓ n :=
  (constantKernelIso (k K) (ℓ ^ n)).symm ≪≫
    ((constantSheaf (J (X K)) G).mapIso (cyclicIso K ℓ n)).symm ≪≫
      nativeResidueIso (X K) ℓ n

private theorem realized_digits (a : ℤ_[ℓ]) (n : ℕ) :
    ((digit ℓ a n : ℤ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

set_option maxHeartbeats 2000000 in
private theorem kernelBoundary_residue (a : ℤ_[ℓ]) (n : ℕ) :
    Sheaf.H.map (kernelResidueIso K ℓ n).hom 1
        (kernelBoundary (k K) (ℓ ^ n) (exponentUnit K (digit ℓ a n : ℤ))) =
      levelEquiv K ℓ n (PadicInt.toZModPow n a) := by
  let i := constantKernelIso (k K) (ℓ ^ n)
  have h : Sheaf.H.map i.inv 1
        (kernelBoundary (k K) (ℓ ^ n) (exponentUnit K (digit ℓ a n : ℤ))) =
      cyclicToRootsHOne K (ℓ ^ n) (PadicInt.toZModPow n a) := by
    change unitBoundary (k K) (ℓ ^ n) (exponentUnit K (digit ℓ a n : ℤ)) = _
    calc
      _ = cyclicToRootsHOne K (ℓ ^ n) ((digit ℓ a n : ℤ) : ZMod (ℓ ^ n)) :=
        (cyclicToRootsHOne_intCast K (ℓ ^ n) (digit ℓ a n : ℤ)).symm
      _ = _ := congrArg (cyclicToRootsHOne K (ℓ ^ n)) (realized_digits ℓ a n)
  simp only [kernelResidueIso, Iso.trans_hom, Iso.symm_hom, Sheaf.H.map_comp_apply, h]
  rfl

set_option maxHeartbeats 2600000 in
/-- Every actual compatible Laurent tuple has one simultaneous product-coefficient representative. -/
theorem exists_product_class (a : ℤ_[ℓ]) :
    ∃ z : Sheaf.H (∏ᶜ (finiteCoefficient (X K) ℓ)) 1, ∀ n,
      Sheaf.H.map (Pi.π (finiteCoefficient (X K) ℓ) n) 1 z = (compatibleEquiv K ℓ a).val n := by
  let T := S K ℓ
  let v := u K ℓ a
  let hS (n : ℕ) := sequence_shortExact (k K) (ℓ ^ n)
  letI : Epi (ExtOneSimultaneousPullback.projection T v) :=
    SheafSimultaneousExtensionEpi.projection_epi (J (X K)) (terminalIsTerminal K) (coverArrow K ℓ)
      T v (covering K ℓ) (fun n ↦ LaurentKummerGeneratorLifts.exists_lift K ℓ (digit ℓ a n) n)
  let hP := ExtOneSimultaneousPullback.sequence_shortExact T v hS
  let z := hP.extClass
  let b := Pi.map (fun n ↦ (kernelResidueIso K ℓ n).hom)
  refine ⟨Sheaf.H.map b 1 z, ?_⟩
  intro n
  let ρ := Pi.π (fun n ↦ (T n).X₁) n
  let π := Pi.π (finiteCoefficient (X K) ℓ) n
  let i := (kernelResidueIso K ℓ n).hom
  have hz : Sheaf.H.map ρ 1 z =
      kernelBoundary (k K) (ℓ ^ n) (exponentUnit K (digit ℓ a n : ℤ)) := by
    calc
      _ = (Ext.mk₀ (v n)).comp (hS n).extClass (zero_add 1) :=
        ExtOneSimultaneousPullback.extension_project T v hS n
      _ = _ := by
        change (Ext.mk₀ (Ext.addEquiv₀ (exponentUnit K (digit ℓ a n : ℤ)))).comp
            (hS n).extClass (zero_add 1) = _
        rw [Ext.mk₀_addEquiv₀_apply] <;> rfl
  calc
    _ = Sheaf.H.map (b ≫ π) 1 z := (Sheaf.H.map_comp_apply b π z).symm
    _ = Sheaf.H.map (ρ ≫ i) 1 z := congrArg (fun d ↦ Sheaf.H.map d 1 z) (Pi.map_π _ n)
    _ = Sheaf.H.map i 1 (Sheaf.H.map ρ 1 z) := Sheaf.H.map_comp_apply ρ i z
    _ = Sheaf.H.map i 1 (kernelBoundary (k K) (ℓ ^ n)
        (exponentUnit K (digit ℓ a n : ℤ))) := congrArg (Sheaf.H.map i 1) hz
    _ = levelEquiv K ℓ n (PadicInt.toZModPow n a) := kernelBoundary_residue K ℓ a n
    _ = _ := (compatibleEquiv_apply K ℓ a n).symm

theorem reduction_surjective : Function.Surjective (reductionMap (X K) ℓ) := by
  intro x
  obtain ⟨a, rfl⟩ := (compatibleEquiv K ℓ).surjective x
  obtain ⟨z, hz⟩ := exists_product_class K ℓ a
  exact exists_lift_of_actual_product_class (X K) ℓ (compatibleEquiv K ℓ a) z hz

/-- The actual integral cohomology of the Laurent line in degree one. -/
def adicEquiv : (X K).EllAdicCohomology ℓ 1 ≃+ ℤ_[ℓ] :=
  (AddEquiv.ofBijective (reductionMap (X K) ℓ)
    ⟨reductionMap_injective (X K) ℓ, reduction_surjective K ℓ⟩).trans (compatibleEquiv K ℓ).symm

/-- The inverse adic coordinate really reduces to the compatible Kummer coordinates. -/
theorem adicEquiv_inverse_reduction (a : ℤ_[ℓ]) :
    reductionMap (X K) ℓ ((adicEquiv K ℓ).symm a) = compatibleEquiv K ℓ a := by
  let e := AddEquiv.ofBijective (reductionMap (X K) ℓ)
    ⟨reductionMap_injective (X K) ℓ, reduction_surjective K ℓ⟩
  exact e.apply_symm_apply (compatibleEquiv K ℓ a)

end
end ManuscriptAudit.ProetaleLaurentNativeAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleLaurentNativeAdicHOne.exists_product_class,
      ``ManuscriptAudit.ProetaleLaurentNativeAdicHOne.reduction_surjective,
      ``ManuscriptAudit.ProetaleLaurentNativeAdicHOne.adicEquiv,
      ``ManuscriptAudit.ProetaleLaurentNativeAdicHOne.adicEquiv_inverse_reduction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
